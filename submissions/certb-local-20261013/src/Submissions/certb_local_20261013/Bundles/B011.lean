/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B006
import Submissions.local44_20261013.Bundles.B007
import Submissions.local44_20261013.Bundles.B008
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalErrorUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.PrimeRows.HighFromMoments ; sha256 f4cd678e0f726d2d08f51bc8f45db8035411e121954067a8cd42face02304d80 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_high_probe_from_raw_moments (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ)
    (hβ : (7/8:ℝ)≤ HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0< sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*(dmax*rmin))
    (hfloorbudget : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+sigma≤7/1200)
    (hcentral : sigma+nu+dyadCost≤ saving) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∃cB κB cH κH C : ℝ,
      0< cB ∧ cB≤1 ∧ 0<κB ∧ 0< cH ∧ cH≤1 ∧ 0<κH ∧ 0< C ∧
    ∀η : Character,∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤ C0 →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) (HeckeZeroSupremum.beta-7/8)
          (if 2*(51/100+e*j)-1≤5/6 then cB else cH)
          (if 2*(51/100+e*j)-1≤5/6 then κB else κH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0< dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith)
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi hfloorbudget
  have hΔ : 0≤ HeckeZeroSupremum.beta-7/8 := by linarith
  have hΔ1 : HeckeZeroSupremum.beta-7/8≤1/8 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,hbound⟩ :=
    actual_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm (HeckeZeroSupremum.beta-7/8) ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ.le (by linarith) hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hmuMargin
  refine ⟨n,hn,cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(13/16+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤ n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤1 := by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2,(hbins u).2.1⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u≤ detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 rows hrows idx grid hlabel hnext hcurrent hmom).2
  have hexp : Z^(3/16+(HeckeZeroSupremum.beta-7/8)-saving+nu+dyadCost)≤
      Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.PrimeRows.HighFromMoments -/

/- BEGIN ORIGINAL MODULE Physical.DiagonalCapacity ; sha256 0e4554aafc0e443d1bd0a09f1dc96bb44c1cc40c81000db17d5c6cf40ab86889 -/
section


/-! The common upper edge used by the physical coefficient boxes pays for
both diagonal moments separately. This allows independent Fourier heights
to be handled by Cauchy--Schwarz without reducing the selected capacity. -/

noncomputable section
namespace Local44.Physical

theorem local_diagonal_capacities {n t n₁ n₂ z : ℝ} (hn : BareWindow n)
    (ht : 0 ≤ t) (htop : t ≤ 3/4000)
    (hn₁ : n₁ ≤ n+t) (hn₂ : n₂ ≤ n+t)
    (hz : z ≤ localCapacity n t) :
    (2*n₁+z ≤ 881/1000 ∧ 2*n₁+(9/2)*z ≤ 100429/100000) ∧
    (2*n₂+z ≤ 881/1000 ∧ 2*n₂+(9/2)*z ≤ 100429/100000) := by
  have h₁ := local_capacity_region hn ht htop hn₁ hn₁ hz
  have h₂ := local_capacity_region hn ht htop hn₂ hn₂ hz
  exact ⟨by constructor <;> linarith [h₁.1,h₁.2],
    by constructor <;> linarith [h₂.1,h₂.2]⟩

/-- The actual local/old/empty dispatch with the two stronger diagonal
capacity inequalities exposed on the local branch. -/
theorem transport_pair_diagonal_dispatch {n t n₁ n₂ z : ℝ}
    (hn : BareWindow n) (ht : 0 ≤ t) (hz0 : 0 ≤ z)
    (hn₁ : n₁ ≤ n+t) (hn₂ : n₂ ≤ n+t)
    (hz : z ≤ transportCapacity n t) :
    (41/100 ≤ n₁ ∧ n₁ ≤ 423/1000 ∧
     41/100 ≤ n₂ ∧ n₂ ≤ 423/1000 ∧
     17/500 ≤ z ∧ z ≤ 37/1000 ∧
     (2*n₁+z ≤ 881/1000 ∧ 2*n₁+(9/2)*z ≤ 100429/100000) ∧
     (2*n₂+z ≤ 881/1000 ∧ 2*n₂+(9/2)*z ≤ 100429/100000)) ∨
    n₁+n₂+(9/2)*z ≤ 1 ∨ z=0 := by
  by_cases hs : t ≤ 3/4000
  · rw [transportCapacity, if_pos hs] at hz
    rcases local_or_old_pair hn ht hs hn₁ hn₂ hz with hlocal | hold
    · obtain ⟨h1,h2,h3,h4,h5,h6,_⟩ := hlocal
      obtain ⟨hc1,hc2⟩ := local_diagonal_capacities hn ht hs hn₁ hn₂ hz
      exact Or.inl ⟨h1,h2,h3,h4,h5,h6,hc1,hc2⟩
    · exact Or.inr (Or.inl (by linarith))
  · rw [transportCapacity, if_neg hs] at hz
    rcases old_capacity_feasible_or_zero hz0 hz with hold | hzero
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr hzero)

end Local44.Physical

#print axioms Local44.Physical.local_diagonal_capacities
#print axioms Local44.Physical.transport_pair_diagonal_dispatch
end
/- END ORIGINAL MODULE Physical.DiagonalCapacity -/

/- BEGIN ORIGINAL MODULE ZetaZeroFree.Analytic.Moments.Exceptional ; sha256 557d9c4955277bc14941169ff554633f17835641c8aa3f8fbc3304f83cdebd31 -/
section




namespace ZetaZeroFree.Analytic.Moments

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentRadialEligibleEnergy
open CenteredMomentLattice QuadraticInitialBound
open CenteredMomentTwist
open CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentCommonMaskExpansion CenteredMomentPlainPositiveScale
local notation "O" => HeckeFamily.O

theorem deleted_plain_bound (a b η : ℝ) (ha : 0 < a) (hη : 0 < η) :
    ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)), Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (ψ : Character), ψ.residue ≠ 1 →
      ∀ (R : Ideal O) (X : ℝ), R ≠ 0 → 0 < X →
        ‖polynomial (excluded ψ R) false W X 0 0‖ ≤
          C * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            (ψ.modulus.absNorm : ℝ) * (R.radical.absNorm : ℝ) ^ η := by
  obtain ⟨S, C₀, hC₀, hplain⟩ := global_positive_scale a b ha
  obtain ⟨C₁, hC₁, hmass⟩ := euler_mass_subpower η hη
  refine ⟨S, C₀ * 9 * C₁, by positivity, ?_⟩
  intro W hs ψ hψ R X hR hX
  let T := CompletedGauss.primeSupport R
  have hT : ∀ P ∈ T, Prime P := CenteredMomentNaturalRowSource.support_prime R
  let D : ℝ := C₀ * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
    (ψ.modulus.absNorm : ℝ) * 9
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hp (U : Finset (Ideal O)) (hU : U ∈ T.powerset) :
      ‖polynomial ψ false W (X / (Ideal.absNorm (∏ P ∈ U, P) : ℝ)) 0 0‖ ≤ D := by
    have hn : 0 < (Ideal.absNorm (∏ P ∈ U, P) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun P hP =>
          (hT P (Finset.mem_powerset.mp hU hP)).ne_zero)))
    simpa [D, show (3 : ℝ) ^ 2 = 9 by norm_num] using hplain W hs ψ hψ _ 0 (div_pos hX hn)
  have he := normalized_finite_deletion_moebius ψ T hT W (schwartz_decayTwo W) X hX
  change polynomial (excluded ψ R) false W X 0 0 = _ at he
  rw [he]
  calc
    _ ≤ ∑ U ∈ T.powerset, ‖plainCoefficient ψ U *
        polynomial ψ false W (X / (Ideal.absNorm (∏ P ∈ U, P) : ℝ)) 0 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ U ∈ T.powerset, weight (∏ P ∈ U, P) * D := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      exact mul_le_mul
        (plainCoefficient_norm ψ U (fun P hP => hT P (Finset.mem_powerset.mp hU hP)))
        (hp U hU) (norm_nonneg _) (weight_nonneg _)
    _ = (∏ P ∈ T, (1 + weight P)) * D := by rw [← Finset.sum_mul, deletion_mass]
    _ ≤ (C₁ * (R.radical.absNorm : ℝ) ^ η) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      have hh := (deletion_le_euler T hT).trans (hmass T hT)
      simpa only [T, CenteredMomentAllocatedNaturalSource.primeSupport_product_radical R hR] using hh
    _ = _ := by dsimp [D]; ring

/-- Induction by a fixed nonprincipal character costs only deletion of its old zeros. -/
theorem induced_mask_polynomial (χ ψ : Character)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) (R : Ideal O) (hR : R ≠ 0)
    (W : ℝ → ℂ) (X σ t : ℝ) :
    polynomial (excluded χ R) false W X σ t =
      polynomial (excluded ψ (χ.modulus * R)) false W X σ t := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold summand HeckeDyadic.coefficient
  rw [CenteredMomentNaturalRowSource.excluded_ideal χ R hR,
    CenteredMomentNaturalRowSource.excluded_ideal ψ (χ.modulus * R)
      (mul_ne_zero χ.modulus_ne_bot hR), hind I.val, IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

/-- A plain mixed endpoint for all rows induced by bounded nonprincipal conductors.
The primitive characters and redundant masks may vary with the row. -/
theorem fixed_induced_mixed (a b ε B Q : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hB : 0 ≤ B) (hQ : 0 < Q) :
    ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ ψ : O → Character) (r : Radial) (R : Ideal O) (Z m X₁ X₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → r.scale = Z ^ m → 0 < X₁ → 0 < X₂ →
        (∀ z, r.keep z → CenteredExceptionalProfile.InducedBy (χ z) (ψ z)) →
        (∀ z, r.keep z → (ψ z).residue ≠ 1) →
        (∀ z, r.keep z → ((ψ z).modulus.absNorm : ℝ) ≤ Q) →
        (∀ z, r.keep z → (((χ z).modulus * R).radical.absNorm : ℝ) ≤ Z ^ B) →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
          C * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 * Z ^ (m + ε) := by
  let η : ℝ := ε / (4 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηB : 4 * (B * η) ≤ ε := by
    have he : η * (4 * (B + 1)) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨S, C₀, hC₀, hplain⟩ := deleted_plain_bound a b η ha hη
  refine ⟨S, C₀ ^ 4 * Q ^ 4, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ ψ r R Z m X₁ X₂ hR hZ hm hscale hX₁ hX₂ hind hψ hmod hmask
  let B₁ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁ : 0 ≤ B₁ := apply_nonneg _ _
  have hB₂ : 0 ≤ B₂ := apply_nonneg _ _
  let D : ℝ := C₀ ^ 2 * (B₁ * B₂) * Q ^ 2 * (Z ^ (B * η)) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hd := diagonalControl_nonneg r.profile
  have hp (z : O) (hk : r.keep z) (W : 𝓢(ℝ, ℂ))
      (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (X : ℝ) (hX : 0 < X) :
      ‖polynomial (excluded (χ z) R) false W X 0 0‖ ≤
        C₀ * (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * Q * Z ^ (B * η) := by
    rw [induced_mask_polynomial (χ z) (ψ z) (hind z hk) R hR]
    have hh := hplain W hs (ψ z) (hψ z hk) ((χ z).modulus * R) X
      (mul_ne_zero (χ z).modulus_ne_bot hR) hX
    apply hh.trans
    gcongr
    · exact hmod z hk
    · apply (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmask z hk) hη.le).trans_eq
      rw [← Real.rpow_mul hz.le]
  have hpoint (z : O) (hk : r.keep z) :
      ‖polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
        polynomial (excluded (χ z) R) false W₂ X₂ 0 0‖ ≤ D := by
    rw [norm_mul]
    exact (mul_le_mul (hp z hk W₁ hs₁ X₁ hX₁) (hp z hk W₂ hs₂ X₂ hX₂)
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp [D, B₁, B₂]; ring)
  have hh := CenteredMomentPlainGlobalEnergy.radial_bound_on_keep _ r D hD hpoint
  change radialEnergy _ r.keep r.profile r.scale ≤ _ at hh
  rw [hscale, max_eq_right (Real.one_le_rpow hZ hm)] at hh
  have hpow : Z ^ m * ((Z ^ (B * η)) ^ 2) ^ 2 ≤ Z ^ (m + ε) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  rw [hscale]
  apply hh.trans
  calc
    _ = (C₀ ^ 4 * Q ^ 4 * diagonalControl r.profile * (B₁ * B₂) ^ 2) *
        (Z ^ m * ((Z ^ (B * η)) ^ 2) ^ 2) := by dsimp [D]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem fixed_induced_mixed_height (a b ε B Q : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hB : 0 ≤ B) (hQ : 0 < Q) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ ψ : O → Character) (r : Radial) (R : Ideal O) (Z m X₁ X₂ t₁ t₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → r.scale = Z ^ m → 0 < X₁ → 0 < X₂ →
        (∀ z, r.keep z → CenteredExceptionalProfile.InducedBy (χ z) (ψ z)) →
        (∀ z, r.keep z → (ψ z).residue ≠ 1) →
        (∀ z, r.keep z → ((ψ z).modulus.absNorm : ℝ) ≤ Q) →
        (∀ z, r.keep z → (((χ z).modulus * R).radical.absNorm : ℝ) ≤ Z ^ B) →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 t₁ *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 t₂) r.keep r.profile r.scale ≤
          C * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
            (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + ε) := by
  obtain ⟨S₀, C₀, hC₀, he⟩ := fixed_induced_mixed a b ε B Q ha hε hB hQ
  obtain ⟨J, S, C₁, hC₁, hheight⟩ := mixed_height_profile_control a b ha S₀
  refine ⟨J, S, C₀ * C₁, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ ψ r R Z m X₁ X₂ t₁ t₂ hR hZ hm hscale hX₁ hX₂ hind hψ hmod hmask
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hsV₁ : Function.support (V₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
  have hsV₂ : Function.support (V₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂
  have hh := he V₁ V₂ hsV₁ hsV₂ χ ψ r R Z m X₁ X₂ hR hZ hm hscale hX₁ hX₂ hind hψ hmod hmask
  rw [mixed_height_energy_eq a b ha χ r R W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂] at hh
  have hd := diagonalControl_nonneg r.profile
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hheight W₁ W₂ hs₁ hs₂ t₁ t₂)
      (mul_nonneg hC₀.le hd)) (Real.rpow_nonneg (zero_le_one.trans hZ) _)).trans_eq
  ring

section CertifiedZeroExtraction
open Filter CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional

lemma natural_energy_eq (Z B radial a b : ℝ) (ha : 0 < a)
    (s : NaturalState Z B radial) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    s.plainEnergy p 0 X₁ X₂ = radialEnergy
      (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false (p.profile 0) X₁ 0 0 *
        polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false (p.profile 1) X₂ 0 0)
      s.radial.keep s.radial.profile s.radial.scale := by
  rw [s.plainEnergy_eq_zero]
  unfold CenteredMomentCoreFloor.zeroEnergy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : s.radial.keep z
  · have hz := s.row_ne_zero z hk
    simp only [ite_eq_left hk]
    rw [CenteredMomentPlainGlobalEnergy.zero_row_norm s.character
      (excluded (naturalPlainCharacter s.character z) s.puncture) s.mask 1 z
      (by simpa [naturalPlainCharacter, hz, NaturalState.mask] using
        (naturalRow s.character z hz).masked_element s.puncture s.puncture_ne_zero)
      (p.profile 0) (p.profile 1) a b ha (p.support 0) (p.support 1)
      ((p.profile 0).smooth ⊤) ((p.profile 1).smooth ⊤) 0 X₁ X₂ hX₁ hX₂,
      norm_mul]
  · simp [hk]

def NonfixedMixedAt (Q : Ideal O) (a b radial B L Mcap ε Z : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState Z B radial, s.fixedModulus = Q → s.width ≤ Mcap →
    ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
    ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      radialEnergy (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false W₁ X₁ 0 t₁ *
        polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false W₂ X₂ 0 t₂) s.radial.keep s.radial.profile s.radial.scale ≤
        C * diagonalControl s.radial.profile *
          ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

theorem zero_at_independent_heights (a b : ℝ) (ha : 0 < a) (S₀ : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ Cheight : ℝ, 0 < Cheight ∧
      ∀ (Q : Ideal O) (radial B L Mcap ε Z C : ℝ) (J₀ : ℕ),
        0 ≤ Z → 0 ≤ C → ZeroAt Q a b radial B L Mcap ε Z J₀ S₀ C →
        NonfixedMixedAt Q a b radial B L Mcap ε Z J S (C * Cheight) := by
  obtain ⟨J, S, Cheight, hCheight, he⟩ := mixed_height_profile_control a b ha S₀
  refine ⟨J, S, Cheight, hCheight, ?_⟩
  intro Q radial B L Mcap ε Z C J₀ hZ hC hz s hQ hw W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hsV₁ : Function.support (V₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
  have hsV₂ : Function.support (V₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂
  let p : Profiles a b := {
    profile := ![V₁, V₂]
    support := by
      intro i
      fin_cases i
      · exact hsV₁
      · exact hsV₂ }
  have hh := hz s hQ hw p 0 X₁ X₂ hX₁ hX₂ hLX₁ hLX₂
  rw [natural_energy_eq Z B radial a b ha s p X₁ X₂ hX₁ hX₂] at hh
  change radialEnergy (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false V₁ X₁ 0 0 * polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false V₂ X₂ 0 0) s.radial.keep s.radial.profile s.radial.scale ≤ _ at hh
  rw [mixed_height_energy_eq a b ha (naturalPlainCharacter s.character) s.radial
    s.puncture W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂] at hh
  simp only [norm_zero, add_zero, one_pow, mul_one] at hh
  have hp : p.control S₀ = (S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁) *
      (S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂) := rfl
  rw [hp] at hh
  have hd := diagonalControl_nonneg s.radial.profile
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (he W₁ W₂ hs₁ hs₂ t₁ t₂) (mul_nonneg hC hd))
    (Real.rpow_nonneg hZ _)).trans_eq
  ring

end CertifiedZeroExtraction

lemma fixed_inducing_natural_character (η : Character) (Q R : Ideal O)
    (hR : R ≠ 0) (z : O) (hz : z ≠ 0)
    (hfixed : CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator R) 1 z) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ Q ≤ ψ.modulus ∧
      CenteredExceptionalProfile.InducedBy (excluded (naturalPlainCharacter η z) R) ψ := by
  obtain ⟨χ, ψ, hprim, hind, hQ, hrow⟩ := hfixed
  refine ⟨ψ, hprim, hQ, HeckeMaskDescent.inducedBy_mask χ
    (excluded (naturalPlainCharacter η z) R) ψ 1 ?_ hind⟩
  intro n
  simp only [isCoprime_one_right, ite_true]
  rw [hrow]
  simpa [naturalPlainCharacter, hz] using (naturalRow η z hz).masked_element R hR n

lemma fixed_inducing_natural_nonprincipal (η : Character) (Q R : Ideal O)
    (hR : R ≠ 0) (z : O) (hz : z ≠ 0)
    (hn : (naturalPlainCharacter η z).residue ≠ 1)
    (hfixed : CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator R) 1 z) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue ≠ 1 ∧
      Q ≤ ψ.modulus ∧
      CenteredExceptionalProfile.InducedBy (excluded (naturalPlainCharacter η z) R) ψ := by
  obtain ⟨ψ, hp, hQ, hind⟩ := fixed_inducing_natural_character η Q R hR z hz hfixed
  have hmask := excludePrimes_mask (naturalPlainCharacter η z)
    (CompletedGauss.primeSupport R) (support_prime R)
  have hχ : (excluded (naturalPlainCharacter η z) R).residue ≠ 1 := by
    intro h
    exact hn ((HeckeFiniteDeletion.principal_iff_of_mask _ _ hmask).mp h)
  refine ⟨ψ, hp, ?_, hQ, hind⟩
  intro h
  exact hχ ((HeckeFiniteDeletion.principal_iff_of_mask _ _ hind).mpr h)

lemma polynomial_excluded_top (χ : Character) (W : ℝ → ℂ) (X σ t : ℝ) :
    polynomial (excluded χ ⊤) false W X σ t = polynomial χ false W X σ t := by
  have hc (I : Ideal O) : IsCoprime I ⊤ := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_right
  unfold polynomial summand HeckeDyadic.coefficient
  simp only [excluded_ideal χ ⊤ top_ne_bot, hc, ite_true]

lemma mixed_radial_partition (χ : O → Character) (r : Radial) (P : O → Prop)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (a b X₁ X₂ t₁ t₂ : ℝ) (hb : 0 ≤ b)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    radialEnergy (fun z => polynomial (χ z) false W₁ X₁ 0 t₁ *
        polynomial (χ z) false W₂ X₂ 0 t₂) r.keep r.profile r.scale =
      radialEnergy (fun z => polynomial (χ z) false W₁ X₁ 0 t₁ *
        polynomial (χ z) false W₂ X₂ 0 t₂) (fun z => r.keep z ∧ P z) r.profile r.scale +
      radialEnergy (fun z => polynomial (χ z) false W₁ X₁ 0 t₁ *
        polynomial (χ z) false W₂ X₂ 0 t₂) (fun z => r.keep z ∧ ¬ P z) r.profile r.scale := by
  have hs (keep : O → Prop) := CenteredMomentRadialPolynomialEnergy.pair_radial_summable
    χ (fun _ => (1 : ℂ)) (fun _ => t₁) (fun _ => t₂) W₁ W₂ a b a b X₁ X₂ 1
    hb hb hX₁ hX₂ hs₁ hs₂ (by simp) keep r.profile r.scale r.scale_pos
  simp only [mul_one] at hs
  unfold radialEnergy
  rw [← Summable.tsum_add (hs (fun z => r.keep z ∧ P z)) (hs (fun z => r.keep z ∧ ¬ P z))]
  apply tsum_congr
  intro z
  by_cases hk : r.keep z <;> by_cases hp : P z <;> simp [hk, hp]

theorem all_natural_mixed_join (a b radial B Bfixed L Mcap ε : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hBfixed : 0 ≤ Bfixed) (hε : 0 < ε)
    (Q : Ideal O) (hQ : Q ≠ 0) (Jn : ℕ) (Sn : Finset (ℕ × ℕ)) (Cn : ℝ) :
    ∃ Jf : ℕ, ∃ Sf : Finset (ℕ × ℕ), ∃ Cf : ℝ, 0 < Cf ∧
      ∀ Z : ℝ, NonfixedMixedAt Q a b radial B L Mcap ε Z Jn Sn Cn →
      ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
      (s.puncture.absNorm : ℝ) ≤ Z ^ B →
      (∀ z, s.radial.keep z →
        ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤ Z ^ Bfixed) →
      ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
        Cn * diagonalControl s.radial.profile *
          ((Sn.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (Sn.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ Jn * (1 + ‖t₂‖) ^ Jn * Z ^ (s.width + ε) +
        Cf * diagonalControl s.radial.profile *
          ((Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ Jf * (1 + ‖t₂‖) ^ Jf * Z ^ (s.rowWidth + ε) := by
  have hQnorm : 0 < (Q.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  obtain ⟨Jf, Sf, Cf, hCf, hf⟩ := fixed_induced_mixed_height a b ε Bfixed Q.absNorm
    ha hε hBfixed hQnorm
  refine ⟨Jf, Sf, Cf, hCf, ?_⟩
  intro Z hn s hw hpuncture hmasked W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  let P : O → Prop := fun z => ¬ CenteredExceptionalProfile.FixedInducingRow s.character Q
    (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator s.puncture) 1 z
  let rn : Radial := { s.radial with keep := fun z => s.radial.keep z ∧ P z }
  let rf : Radial := { s.radial with keep := fun z => s.radial.keep z ∧ ¬ P z }
  let sn : CenteredMomentEnergyState.NaturalState Z B radial := {
    character := s.character, fixedModulus := Q, puncture := s.puncture, radial := rn,
    rowWidth := s.rowWidth, characterWidth := s.characterWidth,
    base_ge_one := s.base_ge_one, row_nonneg := s.row_nonneg, character_nonneg := s.character_nonneg,
    scale_eq := s.scale_eq, modulus_bound := by simpa only [one_mul] using s.modulus_bound,
    puncture_ne_zero := s.puncture_ne_zero, puncture_bound := hpuncture,
    radial_support := s.radial_support, row_ne_zero := fun z hk => s.row_ne_zero z hk.1,
    nonexceptional := fun _ hk => hk.2 }
  have hn' := hn sn rfl hw W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  have hex (z : O) (hk : rf.keep z) := fixed_inducing_natural_nonprincipal s.character Q
    s.puncture s.puncture_ne_zero z (s.row_ne_zero z hk.1) (s.row_nonprincipal z hk.1)
    (Classical.not_not.mp hk.2)
  choose ψ hp hψ hψQ hi using fun z => fun hk : rf.keep z => hex z hk
  let χ : O → Character := fun z => excluded (naturalPlainCharacter s.character z) s.puncture
  let ψf : O → Character := fun z => if hk : rf.keep z then ψ z hk else χ z
  have hi' (z : O) (hk : rf.keep z) : CenteredExceptionalProfile.InducedBy (χ z) (ψf z) := by
    simpa [ψf, hk] using hi z hk
  have hψ' (z : O) (hk : rf.keep z) : (ψf z).residue ≠ 1 := by
    have hψeq : ψf z = ψ z hk := by
      exact dite_eq_left hk
    rw [hψeq]
    exact hψ z hk
  have hmod (z : O) (hk : rf.keep z) : ((ψf z).modulus.absNorm : ℝ) ≤ Q.absNorm := by
    simp only [ψf, dite_eq_left hk]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (hψQ z hk)))
  have hf' := hf W₁ W₂ hs₁ hs₂ χ ψf rf ⊤ Z s.rowWidth X₁ X₂ t₁ t₂ top_ne_bot
    s.base_ge_one s.row_nonneg s.scale_eq hX₁ hX₂ hi' hψ' hmod
    (by intro z hk; simpa [χ] using hmasked z hk.1)
  simp only [polynomial_excluded_top] at hf'
  rw [NaturalPlainState.energy, mixed_radial_partition χ s.radial P W₁ W₂ a b X₁ X₂ t₁ t₂
    hb hs₁ hs₂ hX₁ hX₂]
  exact add_le_add hn' hf'

lemma mixed_uniform_control_mono (S T : Finset (ℕ × ℕ)) (hST : S ⊆ T)
    (J K : ℕ) (hJK : J ≤ K) (W₁ W₂ : 𝓢(ℝ, ℂ)) (t₁ t₂ : ℝ) :
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J ≤
    ((T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
      (1 + ‖t₁‖) ^ K * (1 + ‖t₂‖) ^ K := by
  have hp : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂) ≤
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂) :=
    mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hST) W₁)
      (Seminorm.le_def.mp (Finset.sup_mono hST) W₂) (apply_nonneg _ _) (apply_nonneg _ _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp 2
  have ht₁ := pow_le_pow_right₀ (by linarith [norm_nonneg t₁] : 1 ≤ 1 + ‖t₁‖) hJK
  have ht₂ := pow_le_pow_right₀ (by linarith [norm_nonneg t₂] : 1 ≤ 1 + ‖t₂‖) hJK
  exact mul_le_mul (mul_le_mul hpow ht₁ (by positivity) (by positivity)) ht₂
    (by positivity) (by positivity)

theorem all_natural_mixed_uniform_join (a b radial B Bfixed L Mcap ε : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hBfixed : 0 ≤ Bfixed) (hε : 0 < ε)
    (Q : Ideal O) (hQ : Q ≠ 0) (Jn : ℕ) (Sn : Finset (ℕ × ℕ)) (Cn : ℝ) (hCn : 0 ≤ Cn) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, NonfixedMixedAt Q a b radial B L Mcap ε Z Jn Sn Cn →
      ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
      (s.puncture.absNorm : ℝ) ≤ Z ^ B →
      (∀ z, s.radial.keep z →
        ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤ Z ^ Bfixed) →
      ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
        C * diagonalControl s.radial.profile *
          ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
           (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
          (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε) := by
  obtain ⟨Jf, Sf, Cf, hCf, he⟩ := all_natural_mixed_join a b radial B Bfixed L Mcap ε
    ha hb hBfixed hε Q hQ Jn Sn Cn
  refine ⟨max Jn Jf, Sn ∪ Sf, Cn + Cf, by linarith, ?_⟩
  intro Z hn s hw hpuncture hmasked W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  have hh := he Z hn s hw hpuncture hmasked W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  have hN := mixed_uniform_control_mono Sn (Sn ∪ Sf) Finset.subset_union_left
    Jn (max Jn Jf) (le_max_left _ _) W₁ W₂ t₁ t₂
  have hF := mixed_uniform_control_mono Sf (Sn ∪ Sf) Finset.subset_union_right
    Jf (max Jn Jf) (le_max_right _ _) W₁ W₂ t₁ t₂
  have hd := diagonalControl_nonneg s.radial.profile
  have hz : 0 ≤ Z := zero_le_one.trans s.base_ge_one
  have hZwidth : Z ^ (s.rowWidth + ε) ≤ Z ^ (s.width + ε) :=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by
      dsimp [NaturalPlainState.width]; linarith [s.character_nonneg])
  have hN' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN (mul_nonneg hCn hd)) (Real.rpow_nonneg hz (s.width + ε))
  have hF' := mul_le_mul
    (mul_le_mul_of_nonneg_left hF (mul_nonneg hCf.le hd)) hZwidth
    (Real.rpow_nonneg hz _) (by positivity)
  apply hh.trans
  convert add_le_add hN' hF' using 1 <;> ring

def AllNaturalMixedAt (a b radial B Bfixed L Mcap ε Z : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
    (s.puncture.absNorm : ℝ) ≤ Z ^ B →
    (∀ z, s.radial.keep z →
      ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤ Z ^ Bfixed) →
    ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
    ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
      C * diagonalControl s.radial.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
        (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

def AllNonprincipalAt (a b radial B L Mcap ε Z : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalPlainState Z B radial 1, s.width ≤ Mcap →
    (s.puncture.absNorm : ℝ) ≤ Z ^ B →
    ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
    ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
      C * diagonalControl s.radial.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
        (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

lemma live_masked_modulus_budget (Z B radial Mcap : ℝ)
    (s : NaturalPlainState Z B radial 1) (hw : s.width ≤ Mcap) (hradial : 0 ≤ radial)
    (hcap : (fixedConductorFactor : ℝ) * radial ≤ Z) (z : O)
    (hk : s.restrictLive.radial.keep z) :
    ((excluded (naturalPlainCharacter s.character z) s.puncture).modulus.radical.absNorm : ℝ) ≤
      Z ^ (Mcap + B + 1) := by
  have hz := s.row_ne_zero z hk.1
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  have hzn : ((Ideal.span {z}).absNorm : ℝ) ≤ radial * Z ^ s.rowWidth := by
    rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
    exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hk.2)
  have hη : (s.character.modulus.absNorm : ℝ) ≤ Z ^ s.characterWidth := by
    simpa only [one_mul] using s.modulus_bound
  have hnatural : ((naturalPlainCharacter s.character z).modulus.absNorm : ℝ) ≤
      (fixedConductorFactor : ℝ) * radial * Z ^ s.width := by
    simpa [naturalPlainCharacter, hz, NaturalPlainState.width, add_comm s.rowWidth s.characterWidth]
      using (naturalRow s.character z hz).modulus_power_bound Z s.characterWidth
        s.rowWidth radial hZ hradial hη hzn
  let χ := excluded (naturalPlainCharacter s.character z) s.puncture
  have hrad : (χ.modulus.radical.absNorm : ℝ) ≤ χ.modulus.absNorm := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I := χ.modulus))))
  have hnorm : (χ.modulus.absNorm : ℝ) =
      ((naturalPlainCharacter s.character z).modulus.absNorm : ℝ) *
        (s.puncture.radical.absNorm : ℝ) := by
    change (((naturalPlainCharacter s.character z).modulus *
      ∏ P ∈ CompletedGauss.primeSupport s.puncture, P).absNorm : ℝ) = _
    rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical s.puncture s.puncture_ne_zero]
    simp only [map_mul, Nat.cast_mul]
  apply hrad.trans
  rw [hnorm]
  have hpow := Real.rpow_le_rpow_of_exponent_le s.base_ge_one hw
  have hmod := mul_le_mul hnatural s.puncture_bound (Nat.cast_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hradial) (Real.rpow_nonneg hZ.le _))
  apply hmod.trans
  calc
    _ ≤ (Z * Z ^ Mcap) * Z ^ B := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
      exact mul_le_mul hcap hpow (Real.rpow_nonneg hZ.le _) hZ.le
    _ = (Z ^ (1 : ℝ) * Z ^ Mcap) * Z ^ B := by rw [Real.rpow_one]
    _ = Z ^ (1 + Mcap + B) := by rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    _ = _ := by congr 1; ring


def sourcePlainKeep (η : Character) (z : O) : Prop :=
  z ≠ 0 ∧ (naturalPlainCharacter η z).residue ≠ 1

def sourcePlainState (η : Character) (Φ : 𝓢(ℝ, ℂ)) (radial U δ : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) (hη : (η.modulus.absNorm : ℝ) ≤ U ^ δ) :
    NaturalPlainState U 0 radial 1 where
  character := η
  puncture := 1
  radial := {
    keep := sourcePlainKeep η
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth := 1
  characterWidth := δ
  displayedSupport := ⊤
  displayed_squarefree := by rw [← Ideal.one_eq_top]; exact squarefree_one
  displayed_bound := by simpa using Real.one_le_rpow hU hδ
  displayed_zeros := le_top
  base_ge_one := hU
  row_nonneg := by norm_num
  character_nonneg := hδ
  scale_eq := by simp
  modulus_bound := by simpa only [one_mul] using hη
  puncture_ne_zero := one_ne_zero
  puncture_bound := by simp [Ideal.radical_top]
  radial_support := hs
  row_ne_zero := fun _ hk => hk.1
  row_nonprincipal := fun _ hk => hk.2

lemma plain_state_zero_energy_eq (Z B radial Cfixed a b : ℝ) (ha : 0 < a)
    (s : NaturalPlainState Z B radial Cfixed) (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    CenteredMomentCoreFloor.zeroEnergy s.character
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator s.puncture)
      1 0 W₁ W₂ X₁ X₂ s.radial = s.energy W₁ W₂ X₁ X₂ 0 0 := by
  unfold CenteredMomentCoreFloor.zeroEnergy NaturalPlainState.energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : s.radial.keep z
  · have hz := s.row_ne_zero z hk
    simp only [ite_eq_left hk]
    rw [CenteredMomentPlainGlobalEnergy.zero_row_norm s.character
      (excluded (naturalPlainCharacter s.character z) s.puncture) _ 1 z
      (by simpa [naturalPlainCharacter, hz] using
        (naturalRow s.character z hz).masked_element s.puncture s.puncture_ne_zero)
      W₁ W₂ a b ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤) 0 X₁ X₂ hX₁ hX₂, norm_mul]
  · simp [hk]

section DetectorNaturalSource
open HeckeDetectorRawFiber CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainStateDictionary
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
variable {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem source_retained_plain_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (Φ : 𝓢(ℝ, ℂ)) (radial δ : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) (hη : (η.modulus.absNorm : ℝ) ≤ U ^ δ)
    (j k : ℕ) (σ t : ℝ) :
    retainedSourceEnergy (sourcePlainKeep η) F η ∅ j k σ t Φ =
      (sourcePlainState η Φ radial U δ hU hδ hs hp hη).energy
        ((detectorProfiles F.reverse j k σ t).profile 0)
        ((detectorProfiles F.reverse j k σ t).profile 1)
        (U ^ F.m) (U ^ F.m) 0 0 := by
  let s := sourcePlainState η Φ radial U δ hU hδ hs hp hη
  let p := detectorProfiles F.reverse j k σ t
  rw [← plain_state_zero_energy_eq U 0 radial 1 (1 / 4) (9 / 4) (by norm_num)
    s (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) (U ^ F.m) (U ^ F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)]
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  simp only [plainProfile_eq_detectorSchwartz]
  simp [s, sourcePlainState, p, detectorProfiles, CenteredMomentCoreFloor.zeroEnergy,
    CenteredMomentCoreFloor.zeroRow, CenteredMomentInductionEnergy.energy,
    CenteredMomentRetainedEnergy.positiveSlotRow]

theorem source_retained_plain_bound (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (Φ : 𝓢(ℝ, ℂ)) (radial δ L Mcap loss C : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ))
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) (hη : (η.modulus.absNorm : ℝ) ≤ U ^ δ)
    (hw : 1 + δ ≤ Mcap) (hL : F.m ≤ L)
    (hend : AllNonprincipalAt (1 / 4) (9 / 4) radial 0 L Mcap loss U J S C)
    (j k : ℕ) (σ t : ℝ) :
    retainedSourceEnergy (sourcePlainKeep η) F η ∅ j k σ t Φ ≤
      C * diagonalControl Φ * ((detectorProfiles F.reverse j k σ t).control S) ^ 2 *
        U ^ (1 + δ + loss) := by
  let s := sourcePlainState η Φ radial U δ hU hδ hs hp hη
  let p := detectorProfiles F.reverse j k σ t
  have hX : 0 < U ^ F.m := Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _
  have hXL : U ^ F.m ≤ U ^ L := Real.rpow_le_rpow_of_exponent_le hU hL
  have he := hend s hw (by simp [s, sourcePlainState]) (p.profile 0) (p.profile 1)
    (p.support 0) (p.support 1) (U ^ F.m) (U ^ F.m) 0 0 hX hX hXL hXL
  rw [source_retained_plain_eq F η Φ radial δ hU hδ hs hp hη j k σ t]
  simpa only [s, p, sourcePlainState, NaturalPlainState.width,
    CenteredMomentFiniteProfileExceptional.Profiles.control,
    CenteredMomentFiniteProfileExceptional.sourceControl, norm_zero, add_zero, one_pow, mul_one] using he

end DetectorNaturalSource

/-- D.26, with the first-transform variables measured before rounding. -/
theorem first_exceptional_saving (c D q B g σ : ℝ)
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hg : g ≤ max (D - c) 0 + σ)
    (hcost : max (3 * c - 5 * D) 0 ≤ q + 6 * B) :
    2 * c / 3 - 5 * σ / 6 ≤ c / 6 + 5 * D / 6 + q / 6 + B - 5 * g / 6 := by
  by_cases hD : c ≤ D
  · rw [max_eq_left (by linarith : 0 ≤ D - c)] at hg
    linarith
  · rw [max_eq_right (by linarith : D - c ≤ 0)] at hg
    have hm := le_max_left (3 * c - 5 * D) 0
    linarith

/-- D.28: cancellation is preserved through the final divisor allocation. -/
theorem divisor_cancellation_saving (t r₁ r₂ r : ℝ)
    (_ht₁ : t ≤ r₁) (ht₂ : t ≤ r₂) :
    t - r₁ - r₂ - max (r - r₁) 0 ≤ -r := by
  by_cases h : r₁ ≤ r
  · rw [max_eq_left (by linarith : 0 ≤ r - r₁)]
    linarith
  · rw [max_eq_right (by linarith : r - r₁ ≤ 0)]
    linarith

/-- The exact optimization in D.29. -/
theorem centered_exceptional_deficit (A M v : ℝ) :
    A - 5 * M / 6 - 2 * v / 3 - max (M / 4 - v) 0 ≤ A - M := by
  by_cases h : v ≤ M / 4
  · rw [max_eq_left (by linarith : 0 ≤ M / 4 - v)]
    linarith
  · rw [max_eq_right (by linarith : M / 4 - v ≤ 0)]
    linarith

end
end ZetaZeroFree.Analytic.Moments
end
/- END ORIGINAL MODULE ZetaZeroFree.Analytic.Moments.Exceptional -/

/- BEGIN ORIGINAL MODULE Analytic.CanonicalReconstruction ; sha256 bc96979ca8e6a3b10f8f204ad2d3d9b623cb9c9817012cc4d4d879f39e7ae1a7 -/
section



/-! Signed reconstruction specialized to the source's actual common-support
ideals, active exponents, and chosen radical generator. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open CenteredMomentSecondCanonical CenteredMomentFirstColumns

local notation "O" => ActualEisensteinCubic.O

def activePrimary (C D : Ideal O) (i : ActiveIndex C D) : O :=
  commonPrime C D i.val

theorem activePrimary_span (C D : Ideal O) (hC : Supported C) (i : ActiveIndex C D) :
    Ideal.span {activePrimary C D i} = activePrime C D i :=
  commonPrime_span C D hC i.val

theorem activePrimary_supported (C D : Ideal O) (hC : Supported C) (i : ActiveIndex C D) :
    Supported (Ideal.span {activePrimary C D i}) :=
  commonPrime_supported C D hC i.val

theorem activePrimary_primary (C D : Ideal O) (hC : Supported C) (i : ActiveIndex C D) :
    goodLambda ^ 2 ∣ activePrimary C D i - 1 := by
  exact (CompletedGauss.primaryGenerator_spec i.val.val
    (supported_primaryGenerator_ne_zero _ (commonPrime_supported_ideal C D hC i.val))).2

theorem activeExponent_pos (C D : Ideal O) (i : ActiveIndex C D) :
    0 < activeExponent C D i := by
  exact Nat.pos_of_ne_zero (netExponent_ne_zero _ _ _ i)

theorem activeExponent_lt (C D : Ideal O) (i : ActiveIndex C D) :
    activeExponent C D i < 6 := netExponent_lt_six _ _

theorem actual_active_row_product (C D : Ideal O) (hC : Supported C) (n : O) :
    finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) n =
      ∏ i, idealRowHom n (Ideal.span {activePrimary C D i}) ^ activeExponent C D i := by
  unfold finiteSexticRow
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.pow_apply' _ (Nat.ne_of_gt (activeExponent_pos C D i)),
    activePrimary_span C D hC i, idealRowHom_prime n _ (activeGood C D hC i)]

def leftEffectiveFactor (C D : Ideal O) : O :=
  ∏ i : ActiveIndex C D, activePrimary C D i ^ ((1 + activeExponent C D i) % 6)

def rightEffectiveFactor (C D : Ideal O) : O :=
  ∏ i : ActiveIndex C D, activePrimary C D i ^ ((7 - activeExponent C D i) % 6)

/-- One unit works for every argument, mask divisor and second frequency.
Both canceled-prime masks are retained in the source coefficient identity. -/
theorem actual_first_columns_reconstruct (C D : Ideal O) (hC : Supported C) :
    ∃ u : Oˣ,
      activeConductor C D = (u : O) * ∏ i, activePrimary C D i ∧
      ∀ e n : O, Supported (Ideal.span {n}) → goodLambda ^ 2 ∣ n-1 →
      (leftCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
        idealRowHom (e * (u : O) * leftEffectiveFactor C D) (Ideal.span {n}) *
          (∏ i, sexticReciprocityPhase (activePrimary C D i) n ^ activeExponent C D i) *
          (∏ i, if activeExponent C D i = 5 then
            if IsCoprime n (activePrimary C D i) then (1 : ℂ) else 0 else 1)) ∧
      (rightCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
        idealRowHom (e * (u : O) * rightEffectiveFactor C D) (Ideal.span {n}) *
          (∏ i, sexticReciprocityPhase (activePrimary C D i) n ^ (6-activeExponent C D i)) *
          (∏ i, if activeExponent C D i = 1 then
            if IsCoprime n (activePrimary C D i) then (1 : ℂ) else 0 else 1)) := by
  obtain ⟨u, hu⟩ := prime_modulus_unit_product (activePrime C D) (activePrimary C D)
    (activePrimary_span C D hC)
  change activeConductor C D = _ at hu
  refine ⟨u, hu, ?_⟩
  intro e n hn hnp
  have hrow : finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) =
      fun a => ∏ i, idealRowHom a (Ideal.span {activePrimary C D i}) ^ activeExponent C D i := by
    funext a
    exact actual_active_row_product C D hC a
  rw [hu, hrow]
  constructor
  · exact left_column_reconstruction (activePrimary C D) (activeExponent C D) e u n
      (activeExponent_pos C D) (activeExponent_lt C D) (activePrimary_supported C D hC)
      hn (activePrimary_primary C D hC) hnp
  · letI (i : ActiveIndex C D) : (Ideal.span {activePrimary C D i}).IsMaximal := by
      rw [activePrimary_span C D hC i]
      infer_instance
    have hg (i : ActiveIndex C D) : goodLambda ∉ Ideal.span {activePrimary C D i} := by
      rw [activePrimary_span C D hC i]
      exact activeGood C D hC i
    have hc (i : ActiveIndex C D) : ringChar (O ⧸ Ideal.span {activePrimary C D i}) ≠ 2 := by
      rw [activePrimary_span C D hC i]
      exact common_odd C D hC i.val
    exact right_column_reconstruction (activePrimary C D) (activeExponent C D) e u n
      (activeExponent_pos C D) (activeExponent_lt C D) hg hc (activePrimary_supported C D hC)
      hn (activePrimary_primary C D hC) hnp

#print axioms actual_active_row_product
#print axioms actual_first_columns_reconstruct

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.CanonicalReconstruction -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorUniform ; sha256 678387def93f87fbfcbcb63af1e8f63a2d2d822d743783dbb15c30abfe8eeed4 -/
section



/-! The literal source error family with the refined affine term retained. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

theorem refined_error_uniform_child (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(L:ℝ)(hL:0≤ L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 BR BC θsource:ℝ)
    (hlower:0< lower)(ha0:0< a0)(hθsource:0<θsource):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤ M → ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    Fintype.card α≤ N → lower≤ src.lower → src.upper≤ upper →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0< K → 0≤ sigma → 1≤ cost → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤ Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    (Rpick.absNorm:ℝ)≤ Z^BR → (Cpick.absNorm:ℝ)≤ Z^BC →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
        ((BR+BC)*εmask+(εchild+εremove+(sigma+errorRemoval prime Z k-errorMoving prime Z k)/6+
          (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+θsource)/6+θclip/3+κ*mesh))*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*
        (ratioPenalty dyad)^((1:ℝ)/6)*(1+‖v‖)^(2*(dc+degree+4*n))  :=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=
    refined_error_child_from_bands (α:=α) M H hH
      W aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
  obtain ⟨Zr,hZr,hr⟩:=CenteredMomentFirstAmplifiedPaidReserve.eventually_source_reserve
    N lower upper 1 a0 θsource hlower (by norm_num) ha0 hθsource
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Zi,hZi,hi⟩:=hbound η₀
  refine ⟨max Zi Zr,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlowerBeta hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick hRN hCN B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hZiZ:Zi≤ Z:=(le_max_left _ _).trans hZ
  have hZrZ:Zr≤ Z:=(le_max_right _ _).trans hZ
  have hz:1< Z:=hZi.trans_le hZiZ
  have hh:=hi θ Z hZiZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource
    hK hsigma hcost hasource prime hprime k hk hprimeScale hslot Bp υ v0 hυ
    input hinput
    Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad
    hlowerBeta hphysical family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hupperInput:input.upper≤ upper:=by rw [hinput];exact hupperSrc
  have hchild:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤ N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le B.val).trans hcard
  have herr:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤ N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le Bp.val).trans hchild
  have hsmall:sourceReserve src input C D Z delta reserve cost asource≤ delta+reserve+θsource:=
    hr Z hZrZ src input hcard herr hlowerSrc hupperInput C D hC.1 hD.1
      delta reserve cost asource hdelta hreserve hcost haSource
  have hCp:Cpick≠0:=by rcases hside with rfl|rfl;exact hC₂.1;exact hD₂.1
  have hqpos:0< cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=
    mul_pos (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _)
  have href:0< envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad:=
    envelope_pos _ hqpos C₂ D₂ hC₂ U dyad
  apply hh.trans
  apply CenteredMomentEnergyChildEnvelopeFitting.paid_rhs_fit Cc C₀ C₁ p T Rpick Cpick hRpick hCp
    (family χ) (internalQ Q η₀) dyad v height (dc+degree+4*n) Z BR BC εmask
    _ _ _ _ hCc.le hC₀ hC₁ hheight hz.le hεmask.le hRN hCN
  · linarith
  · exact href.le
  · exact zero_le_one.trans (le_max_left _ _)

#print axioms refined_error_uniform_child
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorUniform -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstKernel ; sha256 c5c15c8eabfb8f90809074659d2390be279709373bcd407695f2c1735752c41d -/
section




/-! Literal first-source block expansion and a common Fourier bound with
all common, ray, and projector labels retained in the same finite sum. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open RayFourExpansion ConcretePrimeRowBridge CenteredMomentChildAssembly
open CenteredMomentFirstColumns CenteredMomentFirstChildBound CenteredMomentMobiusRegroup
open CenteredMomentSmooth CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

namespace FirstJointLabel

abbrev LeftIndex (s : FirstJointLabel ι) := columns s.C s.C s.hC.1 s.data.columns
abbrev RightIndex (s : FirstJointLabel ι) := columns s.C s.D s.hD.1 s.data.columns

def puncture (s : FirstJointLabel ι) : O :=
  primeSubsetGenerator (fun P : CommonIndex s.C s.D => P.val) s.E

def activeRow (s : FirstJointLabel ι) : O → ℂ :=
  finiteSexticRow (activePrime s.C s.D) (activeGood s.C s.D s.hC)
    (activeExponent s.C s.D)

def leftCoefficient (s : FirstJointLabel ι) (t : ℝ) : s.LeftIndex → ℂ :=
  divisorCoefficient s.projector (element s.C s.C s.hC.1 s.data.columns)
    (fun i => coefficient s.parent (fixedBadMask * idealGenerator s.data.R) 1 t
      s.data.beta s.C i * CenteredMomentFirstColumns.leftCoefficient s.puncture
        (activeConductor s.C s.D) s.activeRow (element s.C s.C s.hC.1 s.data.columns i))
    s.leftRay

def rightCoefficient (s : FirstJointLabel ι) (t : ℝ) : s.RightIndex → ℂ :=
  divisorCoefficient s.projector (element s.C s.D s.hD.1 s.data.columns)
    (fun i => coefficient s.parent (fixedBadMask * idealGenerator s.data.R) 1 t
      s.data.beta s.D i * CenteredMomentFirstColumns.rightCoefficient s.puncture
        (activeConductor s.C s.D) s.activeRow (element s.C s.D s.hD.1 s.data.columns i))
    s.rightRay

def leftRowCoefficient (s : FirstJointLabel ι) (t : ℝ) (z : O) (i : s.LeftIndex) : ℂ :=
  s.leftCoefficient t i * gaussRow (element s.C s.C s.hC.1 s.data.columns i)
    (element_supported s.C s.C s.hC.1 s.data.columns i) z

def rightRowCoefficient (s : FirstJointLabel ι) (t : ℝ) (z : O) (i : s.RightIndex) : ℂ :=
  s.rightCoefficient t i * gaussRow (element s.C s.D s.hD.1 s.data.columns i)
    (element_supported s.C s.D s.hD.1 s.data.columns i) (-z)

def leftLog (s : FirstJointLabel ι) (X : ℝ) (i : s.LeftIndex) : ℝ :=
  Real.log (‖eisEmbedding (element s.C s.C s.hC.1 s.data.columns i)‖ ^ 2 / X)

def rightLog (s : FirstJointLabel ι) (X : ℝ) (i : s.RightIndex) : ℝ :=
  Real.log (‖eisEmbedding (element s.C s.D s.hD.1 s.data.columns i)‖ ^ 2 / X)

def kernelBlock (s : FirstJointLabel ι) (t : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (R ρ₀ : ℝ) (x : O → ℝ)
    (A₀ B₀ : ℝ) (q : O → ℂ) : ℂ :=
  ∑ z ∈ rows, q z * ∑ i : s.LeftIndex, ∑ j : s.RightIndex,
    (s.leftRowCoefficient t z i * star (s.rightRowCoefficient t z j)) *
      wholeKernel W V R ρ₀ (x z) (s.leftLog A₀ i) (s.rightLog B₀ j)

theorem leftColumn_eq_window (s : FirstJointLabel ι) (t θ X : ℝ)
    (V : ℝ → ℂ) (z : O) :
    leftColumn Finset.univ (s.leftRowCoefficient t z) V (s.leftLog X) θ =
      leftWindowChild s.data s.parent (fixedBadMask * idealGenerator s.data.R) t
        s.C s.D s.hC s.E s.leftRay s.projector θ X V z := by
  unfold leftColumn leftWindowChild gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  change (s.leftCoefficient t i * _) * _ = (s.leftCoefficient t i * _) * _
  unfold leftLog
  ring

theorem rightColumn_eq_window (s : FirstJointLabel ι) (t θ X : ℝ)
    (V : ℝ → ℂ) (z : O) :
    rightColumn Finset.univ (s.rightRowCoefficient t z) V (s.rightLog X) θ =
      star (rightWindowChild s.data s.parent (fixedBadMask * idealGenerator s.data.R) t
        s.C s.D s.hC s.hD s.E s.rightRay s.projector θ X V (-z)) := by
  unfold rightColumn rightWindowChild gaussPolynomial
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change star (s.rightCoefficient t i * _) * _ =
    star ((s.rightCoefficient t i * star (columnPhase V (s.rightLog X i) θ)) * _)
  simp only [star_mul, star_star]
  ring

/-- The unfiltered divisor pool in the exact source formula. -/
def rawProjectors (s : FirstJointLabel ι) : Finset (Ideal O) :=
  divisorPool (Finset.univ : Finset s.RightIndex)
    (fun j => Ideal.span {element s.C s.D s.hD.1 s.data.columns j})

/-- Zero Möbius coefficients are removed before the joint Cauchy step. -/
def projectors (s : FirstJointLabel ι) : Finset (Ideal O) :=
  CenteredMomentWholeDivisorShell.live s.rawProjectors

theorem projector_squarefree (s : FirstJointLabel ι) (L : Ideal O) (hL : L ∈ s.projectors) :
    Squarefree L := CenteredMomentWholeDivisorShell.live_squarefree s.rawProjectors L hL

theorem projector_ne_zero (s : FirstJointLabel ι) (L : Ideal O) (hL : L ∈ s.projectors) :
    L ≠ 0 := (s.projector_squarefree L hL).ne_zero

theorem projector_moebius_norm (s : FirstJointLabel ι) (L : Ideal O) (hL : L ∈ s.projectors) :
    ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ = 1 := by
  simp only [(s.projector_squarefree L hL).moebius_eq,Int.cast_pow,Int.cast_neg,Int.cast_one,
    norm_pow,norm_neg,norm_one,one_pow]

def childLabel (s : FirstJointLabel ι) (L : Ideal O) (χ ξ : RayCharacter) : FirstJointLabel ι :=
  { s with projector := L, leftRay := χ, rightRay := ξ⁻¹ }

/-- Exact source identity, before any norms or label estimates. -/
theorem block_eq_kernel_children (s : FirstJointLabel ι) (t : ℝ)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    block s.parent (fixedBadMask * idealGenerator s.data.R) 1 t s.data.columns s.data.beta
      s.C s.D s.hC s.hD s.E rows W V K K₀ H₀ A₀ B₀ =
    scalar s.C s.D s.hC s.E K A₀ B₀ *
      ∑ L ∈ s.projectors, (UniqueFactorizationMonoid.moebius L : ℂ) *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
          (s.childLabel L χ ξ).kernelBlock t rows W V (K₀ * H₀ / (A₀ * B₀))
            (Real.log ((K / ‖eisEmbedding s.puncture‖ ^ 2 /
              ‖eisEmbedding (activeConductor s.C s.D)‖ ^ 2) / K₀))
            (fun z => Real.log (‖eisEmbedding z‖ ^ 2 / H₀)) A₀ B₀
            (fun z => star (s.activeRow z) * s.activeRow s.puncture) := by
  rw [projectors,←CenteredMomentWholeDivisorShell.sum_moebius_live]
  rw [block_eq_whole s.parent (fixedBadMask * idealGenerator s.data.R) 1 t
    s.data.columns s.data.beta s.C s.D s.hC s.hD s.hCD s.E rows hrows W V
    K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀]
  exact congrArg (fun z : ℂ => scalar s.C s.D s.hC s.E K A₀ B₀ * z)
    (first_row_children rows Finset.univ Finset.univ
      (element s.C s.C s.hC.1 s.data.columns) (element s.C s.D s.hD.1 s.data.columns)
      (element_supported s.C s.C s.hC.1 s.data.columns)
      (element_supported s.C s.D s.hD.1 s.data.columns)
      (element_primary s.C s.C s.hC.1 s.data.columns)
      (element_primary s.C s.D s.hD.1 s.data.columns)
      (fun i => coefficient s.parent (fixedBadMask * idealGenerator s.data.R) 1 t s.data.beta s.C i)
      (fun i => coefficient s.parent (fixedBadMask * idealGenerator s.data.R) 1 t s.data.beta s.D i)
      s.puncture (activeConductor s.C s.D) s.activeRow
      (finiteSexticRow_mul _ _ _) (fun z => star (s.activeRow z))
      (fun z i j => wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
        (Real.log ((K / ‖eisEmbedding s.puncture‖ ^ 2 /
          ‖eisEmbedding (activeConductor s.C s.D)‖ ^ 2) / K₀))
        (Real.log (‖eisEmbedding z‖ ^ 2 / H₀)) (s.leftLog A₀ i) (s.rightLog B₀ j)))


end FirstJointLabel

/-- A source-child estimate at one common Fourier height. The outer
label may change every kernel scale, both characters, and the projector. -/
theorem joint_first_kernel_from_window (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (decay J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (t R ρ₀ A₀ B₀ : Λ → ℝ) (x : Λ → O → ℝ) (η : Λ → ℂ) (q : Λ → O → ℂ),
      (∀ l, 0 < R l) → (∀ l ∈ labels, ∀ z ∈ rows, ‖η l * q l z‖ ≤ 1) →
      (∀ l ∈ labels, ‖V 0 (ρ₀ l)‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (x l z)‖ ≤ 1) →
      ∀ E : ℝ,
      (∀ θ : ℝ, (∑ l ∈ labels, ∑ z ∈ rows,
        ‖leftWindowChild (s l).data (s l).parent
          (fixedBadMask * idealGenerator (s l).data.R) (t l)
          (s l).C (s l).D (s l).hC (s l).E (s l).leftRay (s l).projector θ (A₀ l) (V 2) z‖ *
        ‖rightWindowChild (s l).data (s l).parent
          (fixedBadMask * idealGenerator (s l).data.R) (t l)
          (s l).C (s l).D (s l).hC (s l).hD (s l).E (s l).rightRay (s l).projector
          θ (B₀ l) (V 3) (-z)‖) ≤ E * (1 + ‖θ‖) ^ J) →
      ‖∑ l ∈ labels, (((1 + R l) ^ decay : ℝ) : ℂ) * η l *
        (s l).kernelBlock (t l) rows W V (R l) (ρ₀ l) (x l) (A₀ l) (B₀ l) (q l)‖ ≤ C * E := by
  obtain ⟨C, hC, hc⟩ := whole_kernel_joint_estimate W V M hM hV decay J
  refine ⟨C, hC, ?_⟩
  intro Λ inst labels rows s t R ρ₀ A₀ B₀ x η q hR hη hV₀ hV₁ E he
  have h := hc (labels ×ˢ rows)
    (fun k => (Finset.univ : Finset (s k.1).LeftIndex))
    (fun k => (Finset.univ : Finset (s k.1).RightIndex))
    (fun k => (s k.1).leftRowCoefficient (t k.1) k.2)
    (fun k => (s k.1).rightRowCoefficient (t k.1) k.2)
    (fun k => (s k.1).leftLog (A₀ k.1)) (fun k => (s k.1).rightLog (B₀ k.1))
    (fun k => R k.1) (fun k => ρ₀ k.1) (fun k => x k.1 k.2)
    (fun k => η k.1 * q k.1 k.2) (fun k => hR k.1)
    (fun k hk => hη k.1 (Finset.mem_product.mp hk).1 k.2 (Finset.mem_product.mp hk).2)
    (fun k hk => hV₀ k.1 (Finset.mem_product.mp hk).1)
    (fun k hk => hV₁ k.1 (Finset.mem_product.mp hk).1 k.2 (Finset.mem_product.mp hk).2)
    E (by
      intro θ
      simp only [Finset.sum_product, FirstJointLabel.leftColumn_eq_window,
        FirstJointLabel.rightColumn_eq_window, norm_star]
      exact he θ)
  simpa only [Finset.sum_product, FirstJointLabel.kernelBlock, Finset.mul_sum, mul_assoc] using h


namespace FirstJointLabel

abbrev SourceIndex (s : FirstJointLabel ι) :=
  ↥(s.projectors) × RayCharacter × RayCharacter

def sourceChild (s : FirstJointLabel ι) (i : s.SourceIndex) : FirstJointLabel ι :=
  s.childLabel i.1.val i.2.1 i.2.2

def sourceWeight (s : FirstJointLabel ι) (K A₀ B₀ : ℝ) (i : s.SourceIndex) : ℂ :=
  scalar s.C s.D s.hC s.E K A₀ B₀ *
    (UniqueFactorizationMonoid.moebius i.1.val : ℂ) * pairCoeff firstPhaseTable i.2.1 i.2.2

def sourcePhase (s : FirstJointLabel ι) (z : O) : ℂ :=
  star (s.activeRow z) * s.activeRow s.puncture

theorem sourcePhase_norm (s : FirstJointLabel ι) (z : O) : ‖s.sourcePhase z‖ ≤ 1 := by
  simp only [sourcePhase, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ z)).trans
    (QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ s.puncture)

def sourceRowLog (s : FirstJointLabel ι) (K K₀ : ℝ) : ℝ :=
  Real.log ((K / ‖eisEmbedding s.puncture‖ ^ 2 /
    ‖eisEmbedding (activeConductor s.C s.D)‖ ^ 2) / K₀)

def sourceBlock (s : FirstJointLabel ι) (t : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (K K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  block s.parent (fixedBadMask * idealGenerator s.data.R) 1 t s.data.columns s.data.beta
    s.C s.D s.hC s.hD s.E rows W V K K₀ H₀ A₀ B₀

def windowPair (s : FirstJointLabel ι) (t θ X Y : ℝ) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset O) : ℝ :=
  ∑ z ∈ rows,
    ‖leftWindowChild s.data s.parent (fixedBadMask * idealGenerator s.data.R) t
      s.C s.D s.hC s.E s.leftRay s.projector θ X (V 2) z‖ *
    ‖rightWindowChild s.data s.parent (fixedBadMask * idealGenerator s.data.R) t
      s.C s.D s.hC s.hD s.E s.rightRay s.projector θ Y (V 3) (-z)‖

theorem sourceBlock_eq_sum (s : FirstJointLabel ι) (t : ℝ)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    s.sourceBlock t rows W V K K₀ H₀ A₀ B₀ =
      ∑ i : s.SourceIndex, s.sourceWeight K A₀ B₀ i *
        (s.sourceChild i).kernelBlock t rows W V (K₀ * H₀ / (A₀ * B₀))
          (s.sourceRowLog K K₀) (fun z => Real.log (‖eisEmbedding z‖ ^ 2 / H₀))
          A₀ B₀ s.sourcePhase := by
  rw [sourceBlock, s.block_eq_kernel_children t rows hrows W V
    K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀]
  simp only [SourceIndex, Fintype.sum_prod_type,
    sourceWeight, sourceChild, sourceRowLog, Finset.mul_sum, mul_assoc]
  exact (Finset.sum_coe_sort s.projectors _).symm

end FirstJointLabel

def firstSourceLabels {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (s : Λ → FirstJointLabel ι) :
    Finset ((l : Λ) × (s l).SourceIndex) :=
  labels.sigma (fun _l => Finset.univ)

/-- The literal summed source blocks are controlled by the single joint
window norm. Every actual first projector and both ray labels occur in
`firstSourceLabels`; no cardinality or supremum is taken. -/
theorem joint_first_blocks_from_window (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (decay J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ) (η : Λ → ℂ),
      (∀ z ∈ rows, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, ∀ i : (s l).SourceIndex,
        ‖η l * (s l).sourceWeight (K l) (A₀ l) (B₀ l) i‖ ≤ 1) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (K l) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ E : ℝ,
      (∀ θ : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).windowPair (t k.1) θ (A₀ k.1) (B₀ k.1) V rows) ≤
          E * (1 + ‖θ‖) ^ J) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) * η l *
        (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ ≤ C * E := by
  obtain ⟨C, hC, hc⟩ := joint_first_kernel_from_window (ι := ι) W V M hM hV decay J
  refine ⟨C, hC, ?_⟩
  intro Λ inst labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀ hη hV₀ hV₁ E he
  have h := hc (firstSourceLabels labels s) rows
    (fun k => (s k.1).sourceChild k.2) (fun k => t k.1)
    (fun k => K₀ k.1 * H₀ k.1 / (A₀ k.1 * B₀ k.1))
    (fun k => (s k.1).sourceRowLog (K k.1) (K₀ k.1))
    (fun k => A₀ k.1) (fun k => B₀ k.1)
    (fun k z => Real.log (‖eisEmbedding z‖ ^ 2 / H₀ k.1))
    (fun k => η k.1 * (s k.1).sourceWeight (K k.1) (A₀ k.1) (B₀ k.1) k.2)
    (fun k => (s k.1).sourcePhase)
    (fun k => div_pos (mul_pos (hK₀ k.1) (hH₀ k.1)) (mul_pos (hA₀ k.1) (hB₀ k.1)))
    (fun k hk z hz => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (hη k.1 (Finset.mem_sigma.mp hk).1 k.2)).trans ((s k.1).sourcePhase_norm z))
    (fun k hk => hV₀ k.1 (Finset.mem_sigma.mp hk).1)
    (fun k hk z hz => hV₁ k.1 (Finset.mem_sigma.mp hk).1 z hz) E he
  have hi (l : Λ) : (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l) =
      ∑ i : (s l).SourceIndex, (s l).sourceWeight (K l) (A₀ l) (B₀ l) i *
        ((s l).sourceChild i).kernelBlock (t l) rows W V (K₀ l * H₀ l / (A₀ l * B₀ l))
          ((s l).sourceRowLog (K l) (K₀ l))
          (fun z => Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l)) (A₀ l) (B₀ l) (s l).sourcePhase :=
    (s l).sourceBlock_eq_sum (t l) rows hrows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)
      (hK l) (hK₀ l) (hH₀ l) (hA₀ l) (hB₀ l)
  simp_rw [hi]
  simpa only [firstSourceLabels, Finset.sum_sigma, Finset.mul_sum, mul_assoc] using h


/-- A literal source adapter from joint common energies at common Fourier
heights to the summed first blocks. The complete projector and ray labels
remain inside both input energies throughout the two Fourier windows. -/
theorem joint_first_blocks_from_common_energy
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay P₁ P₂ J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ) (η : Λ → ℂ),
      (∀ z ∈ rows, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, ∀ i : (s l).SourceIndex,
        ‖η l * (s l).sourceWeight (K l) (A₀ l) (B₀ l) i‖ ≤ 1) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (K l) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows,
        1 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ θ w : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).leftEnergy
          (t k.1 + 2 * Real.pi * (w - θ)) (U k) (H k)) ≤
            (E₁ * ((1 + ‖θ‖) ^ P₁) ^ 2) * (1 + ‖w‖) ^ (2 * J₁)) →
      (∀ θ w : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightEnergy
          (t k.1 + 2 * Real.pi * (w - (-θ))) (U k) (H k)) ≤
            (E₂ * ((1 + ‖θ‖) ^ P₂) ^ 2) * (1 + ‖w‖) ^ (2 * J₂)) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) * η l *
        (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ ≤
          C * (Real.sqrt E₁ * Real.sqrt E₂) := by
  let I₁ := jointColumnMoment (V 2) hV₂c hV₂s J₁
  let I₂ := jointColumnMoment (fun x => star (V 3 x))
    (conjugate_compact (V 3) hV₃c) (conjugate_smooth (V 3) hV₃s) J₂
  have hI₁ : 0 ≤ I₁ := jointColumnMoment_nonneg _ _ _ _
  have hI₂ : 0 ≤ I₂ := jointColumnMoment_nonneg _ _ _ _
  obtain ⟨C, hC, hc⟩ := joint_first_blocks_from_window (ι := ι) W V M hM hV decay (P₁ + P₂)
  refine ⟨C * (I₁ * I₂), mul_nonneg hC (mul_nonneg hI₁ hI₂), ?_⟩
  intro Λ inst labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀ hη hV₀ hV₁
    U H hH hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hwindow (θ : ℝ) :
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).windowPair (t k.1) θ (A₀ k.1) (B₀ k.1) V rows) ≤
        ((Real.sqrt E₁ * Real.sqrt E₂) * (I₁ * I₂)) * (1 + ‖θ‖) ^ (P₁ + P₂) := by
    have hh := joint_first_window_abs_bound (firstSourceLabels labels s) rows
      (fun k => (s k.1).sourceChild k.2) (fun k => t k.1) (fun k => t k.1)
      (fun k => A₀ k.1) (fun k => B₀ k.1) (fun k _ => hA₀ k.1) (fun k _ => hB₀ k.1) θ
      (V 2) hV₂c hV₂s (V 3) hV₃c hV₃s U H hH hU hmajor J₁ J₂
      (E₁ * ((1 + ‖θ‖) ^ P₁) ^ 2) (E₂ * ((1 + ‖θ‖) ^ P₂) ^ 2)
      (mul_nonneg hE₁ (sq_nonneg _)) (mul_nonneg hE₂ (sq_nonneg _))
      (hleft θ) (hright θ)
    change _ ≤ (Real.sqrt (E₁ * ((1 + ‖θ‖) ^ P₁) ^ 2) * I₁) *
      (Real.sqrt (E₂ * ((1 + ‖θ‖) ^ P₂) ^ 2) * I₂) at hh
    rw [Real.sqrt_mul hE₁, Real.sqrt_mul hE₂,
      Real.sqrt_sq (by positivity : 0 ≤ (1 + ‖θ‖) ^ P₁),
      Real.sqrt_sq (by positivity : 0 ≤ (1 + ‖θ‖) ^ P₂)] at hh
    simpa only [FirstJointLabel.windowPair, FirstJointLabel.leftWindowValue,
      FirstJointLabel.rightWindowValue, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := hc labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀
    hη hV₀ hV₁ ((Real.sqrt E₁ * Real.sqrt E₂) * (I₁ * I₂)) hwindow
  convert hh using 1
  ring

#print axioms joint_first_blocks_from_common_energy

#print axioms joint_first_blocks_from_window

#print axioms FirstJointLabel.block_eq_kernel_children
#print axioms joint_first_kernel_from_window
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstKernel -/
