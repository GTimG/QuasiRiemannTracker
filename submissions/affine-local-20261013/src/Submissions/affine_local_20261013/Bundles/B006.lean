/-
Affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 at tracker revision 2c3df3b.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B000
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalMaskedFloor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorCollected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NormalizedTransportSaving

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Energy.CertifiedExistence ; sha256 2d48b75fdd14ba8eabb428f79f98e0a6e532c28083075bacf16e1d57f020d7a9 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCertifiedExistence
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCappedAnalyticSuccessor CenteredMomentEnergyCappedRadialTransport
open CenteredMomentEnergyWidthSchedule
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(hrad:2≤ radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∀k:ℕ,k≤ count Mcap ε→
      CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k< count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
      k hstep hprevious

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(_hrad:0< radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε hbeta hκ _ le_rfl

end SevenEighths.CenteredMomentEnergyCertifiedExistence

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Energy.CertifiedExistence -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCollected ; sha256 158f5a3d94c14d6f927d5aba0323785d4e7f843d41ef905bb04535741b79ca4a -/
section


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
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
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃cB κB cH κH C : ℝ,0< cB ∧ cB≤1 ∧ 0<κB ∧ 0< cH ∧ cH≤1 ∧ 0<κH ∧ 0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(13/16+ζ)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u≤ n ∧ grid u≤ m ∧ grid u≠0 ∧ 51/100+e*grid u≤1) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) Δ
          (if 2*(51/100+e*j)-1≤5/6 then cB else cH)
          (if 2*(51/100+e*j)-1≤5/6 then κB else κH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,hbound⟩ :=
    actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  have hellpos (j : Fin N) : 0< ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨cB,κB,cH,κH,Cd*(n+1:ℕ)*(m+1:ℕ)*C,hcB,hcB1,hκB,hcH,hcH1,hκH,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (13/16+ζ) hdmin hdmin1 hmargin hconductor,
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu)
  have hD : 0≤ D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(13/16+ζ)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤ D := by
    let Rk := rows∩dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij⊆Rk := Finset.filter_subset _ _
    have hsub : Rij⊆rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
        (hne'.mono hsubk)
      obtain ⟨u,hu⟩ := hne'
      have huj : grid u=j := ((mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j≠0 := huj ▸ (hlabels u (hsub hu)).2.2.1
      have ha : 51/100<51/100+e*j := by
        have hjp : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51/100+e*j≤1 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hbounded := hb (sourceDyadConductor Z margin k) hgeo.2.2.1 hgeo.2.2.2.1
        (sourceDyadExponent Z k) (51/100+e*j) C0 hgeo.1 hgeo.2.1
        (by unfold sourceDyadConductor;linarith) ha ha' hC0 Rij
        (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
        (fun u hu=> hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        hnext' hcurrent' (fun t ht=> hmom k hk i hi j hj ⟨u,hu⟩ t ht)
      exact hbounded.2
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(13/16+ζ)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(13/16+ζ)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (Z^τ) idx grid n m
        (fun u hu=>⟨(hlabels u (Finset.mem_inter.mp hu).1).1,(hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
      dsimp only [F]
      rw [hpart,Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=> hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(13/16+ζ))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (13/16+ζ) hZ.le (by linarith)) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (3/16+Δ-saving+nu) dyadCost];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCollected -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.PrimeRows.NonfloorTransport ; sha256 43c466c09b82882eff832604a9371bfc03ac6894aaefbff9f8903bc7e680306e -/
section




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
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem nonfloorTransportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_nonfloor_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0< a) (hab : a≤ b) (hB : 0≤ B) (hmin : 0< ellMin) (hnu : 0< nu)
    (hβ : (7/8:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0< sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*ellMin) (hlarge : sigma+nu≤ saving+3/16)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0< eps) (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax)
    (hrmin : 0< rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hmargin : 0< margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε< rmin*mesh)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (hcap : 13/16+ζ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (hfloorbudget : 2*ζ+26*e+(K+8)*eps+loss+mesh/6+nu+sigma≤7/1200) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∀η : Character,∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := nonfloorTransportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
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
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid) T hT WC Yp
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,htransport⟩ := actual_normalized_probe_transport_saving M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    sigma hsigma hgeometric hprincipal hwindow hlarge
  obtain ⟨Cf,hCf,hfloor⟩ := actual_floor_rows_saving M H hH K n e eps a b B R dmin dmax rmin τ ε κ cost mesh
    (1/100) margin loss he he' heps ha hab hB hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    (by norm_num) hphasebudget hphasegap hmargin hheight hloss S hS hfirst hmax ell hellinj helllo hellhi
    W hsupp hW hWB hcompact hne hellsum W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    nu hnu ζ sigma hζ.le (by linarith) hsigma hfloorbudget
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  let C := Ct+Cf*(η.modulus.absNorm:ℝ)^(2*eps)
  have hC : 0< C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [htransport,hfloor η,eventually_ge_atTop (1:ℝ)] with Z ht hf hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  let Yp : Fin K→ℝ := fun j=> Z^(ell j)
  let T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := nonfloorTransportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let rows := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))
  let floors := supportedFloorRows S hmax rows grid
  have hrows : ∀u∈floors,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(dmax-margin) := by
    intro u hu
    rcases (mem_supportedFloorRows S hmax rows grid u).mp hu with ⟨hur,hcal,hg⟩
    have hm := mem_rowBand.mp hur
    exact ⟨hm.1,hm.2.1,hcal,hm.2.2.le.trans (Real.rpow_le_rpow_of_exponent_le hZ hcap)⟩
  have hnorms : ∀u∈floors,rowNorm u≤ Z^((13/16:ℝ)+ζ) := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedFloorRows S hmax rows grid u).mp hu).1).2.2.le
  have hfloorbin : ∀u∈floors,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e := by
    intro u hu
    have hg := ((mem_supportedFloorRows S hmax rows grid u).mp hu).2.2
    have hh := (hbins u).2.2.2.2.1
    simpa only [hg,Nat.cast_zero,mul_zero,add_zero] using hh
  have hb := (hf dmax hdRange le_rfl (13/16+ζ) (by linarith) le_rfl floors hrows hnorms idx
    (fun u hu=>(hlabels u).2.1) hfloorbin).2
  have hsplit := finiteCentralCubeRows_supported_split S hS hmax η rows T hT WC Yp W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e grid (fun u=>(3*idx u+1:ℕ)*Z^τ)
  change _≤ Ct*Z^(HeckeZeroSupremum.beta-11/16-sigma) at herror
  rw [hsplit] at herror
  have hh := normalized_nonfloor_error _ _ _ _ _ _ _ herror hb
  apply hh.trans
  have hp : Z^(3/16-sigma)≤ Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ Ct*Z^(HeckeZeroSupremum.beta-11/16-sigma)+
      (Cf*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by gcongr
    _ = _ := by dsimp [C];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.PrimeRows.NonfloorTransport -/

/- BEGIN ORIGINAL MODULE Physical.Capacity ; sha256 ff07e642eaf3d80458841fb8695a413569f1f2364becd31651ad33c99ec4b059 -/
section






/-! Exact capacities for the actual numerator's coefficient-dilation boxes.
These are arithmetic transport lemmas, not a marked-moment theorem. -/

noncomputable section
namespace Local44.Physical

def baseCapacity (n : ℝ) : ℝ := (10037/10000 - 2*n) / (9/2)
def localCapacity (n t : ℝ) : ℝ := max 0 ((10037/10000 - 2*(n+t)) / (9/2))
def oldCapacity (n t : ℝ) : ℝ := max 0 ((1 - 2*(n+t)) / (9/2))
def transportCapacity (n t : ℝ) : ℝ :=
  if t ≤ 3/4000 then localCapacity n t else oldCapacity n t

def BareWindow (n : ℝ) : Prop := 419/1000 ≤ n ∧ n ≤ 422/1000

theorem baseCapacity_bounds {n : ℝ} (hn : BareWindow n) :
    1597/45000 ≤ baseCapacity n ∧ baseCapacity n ≤ 1657/45000 := by
  rcases hn with ⟨hlo,hhi⟩
  dsimp [baseCapacity]
  constructor <;> linarith

theorem local_capacity_window {n t : ℝ} (hn : BareWindow n)
    (ht : 0 ≤ t) (htop : t ≤ 3/4000) :
    419/1000 ≤ n+t ∧ n+t ≤ 1691/4000 ∧
    791/22500 ≤ localCapacity n t ∧ localCapacity n t ≤ 1657/45000 ∧
    2*(n+t)+(9/2)*localCapacity n t = 10037/10000 ∧
    2*(n+t)+localCapacity n t ≤ 79259/90000 := by
  rcases hn with ⟨hlo,hhi⟩
  have hraw : 0 ≤ (10037/10000-2*(n+t))/(9/2:ℝ) := by linarith
  rw [localCapacity,max_eq_right hraw]
  refine ⟨by linarith,by linarith,by linarith,by linarith,?_,by linarith⟩
  ring

/-- The affine defect allowance and the original source-volume cap are both retained. -/
theorem local_capacity_region {n t n₁ n₂ z : ℝ} (hn : BareWindow n)
    (ht : 0 ≤ t) (htop : t ≤ 3/4000)
    (hn₁ : n₁ ≤ n+t) (hn₂ : n₂ ≤ n+t) (hz : z ≤ localCapacity n t) :
    n₁+n₂+z ≤ 881/1000 ∧ n₁+n₂+(9/2)*z ≤ 10037/10000 := by
  obtain ⟨_,_,_,_,hcapacity,hvolume⟩ := local_capacity_window hn ht htop
  constructor <;> linarith

theorem transportCapacity_nonneg (n t : ℝ) : 0 ≤ transportCapacity n t := by
  unfold transportCapacity
  split_ifs <;> exact le_max_left _ _

theorem transportCapacity_le_base {n t : ℝ} (hn : BareWindow n) (ht : 0 ≤ t) :
    transportCapacity n t ≤ baseCapacity n := by
  have hb := (baseCapacity_bounds hn).1
  unfold transportCapacity localCapacity oldCapacity
  split_ifs with hs
  · apply max_le
    · linarith
    · dsimp [baseCapacity]
      linarith
  · apply max_le
    · linarith
    · rcases hn with ⟨hlo,hhi⟩
      dsimp [baseCapacity]
      linarith

theorem transportCapacity_le_supply {n t L : ℝ} (hn : BareWindow n)
    (ht : 0 ≤ t) (hL : baseCapacity n ≤ L) : transportCapacity n t ≤ L :=
  (transportCapacity_le_base hn ht).trans hL

/-- The old branch repays the affine allowance once the local branch ends. -/
theorem transport_capacity_loss {n t : ℝ} (ht : 0 ≤ t) :
    baseCapacity n - transportCapacity n t ≤ 2*t := by
  unfold transportCapacity
  split_ifs with hs
  · have hcap : (10037/10000-2*(n+t))/(9/2:ℝ) ≤ localCapacity n t :=
      le_max_right _ _
    dsimp [baseCapacity]
    linarith
  · have hcap : (1-2*(n+t))/(9/2:ℝ) ≤ oldCapacity n t := le_max_right _ _
    dsimp [baseCapacity]
    linarith

/-- The original weighted coefficient mass pays every free shift. -/
theorem transport_repayment {n t δ q : ℝ} (hn : BareWindow n)
    (ht : 0 ≤ t) (hq : 0 ≤ q) (hqδ : q ≤ δ/2) :
    q*baseCapacity n/2 ≤ δ*t/2 + q*transportCapacity n t/2 := by
  have hgap := mul_le_mul_of_nonneg_left (transport_capacity_loss (n := n) ht) hq
  have hqt := mul_le_mul_of_nonneg_right hqδ ht
  nlinarith

/-- Dilation-box upper-edge and annular padding cost only their explicit loss. -/
theorem transport_repayment_padded {n v ξ a δ q : ℝ} (hn : BareWindow n)
    (hv : 0 ≤ v) (hξ : 0 ≤ ξ) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (hqδ : q ≤ δ/2) :
    -δ*v/2 - q*transportCapacity n (v+ξ+a)/2 ≤
      -q*baseCapacity n/2 + δ*(ξ+a)/2 := by
  have hh := transport_repayment hn (by linarith : 0 ≤ v+ξ+a) hq hqδ
  nlinarith

/-- The old moment handles short selected supply throughout the local square. -/
theorem old_capacity_of_short {n₁ n₂ z : ℝ}
    (hn₁ : n₁ ≤ 423/1000) (hn₂ : n₂ ≤ 423/1000) (hz : z ≤ 17/500) :
    n₁+n₂+(9/2)*z ≤ 999/1000 := by linarith

/-- One downward plain scale also falls strictly inside the old moment. -/
theorem old_capacity_of_downward {n₁ n₂ z : ℝ}
    (hn₁ : n₁ ≤ 423/1000) (hn₂ : n₂ ≤ 423/1000) (hz : z ≤ 37/1000)
    (hdown : n₁ ≤ 41/100 ∨ n₂ ≤ 41/100) :
    n₁+n₂+(9/2)*z ≤ 1999/2000 := by
  rcases hdown with hdown | hdown <;> linarith

/-- Dispatch the literal pair either into the new local window or the old one. -/
theorem local_or_old_pair {n t n₁ n₂ z : ℝ} (hn : BareWindow n)
    (ht : 0 ≤ t) (htop : t ≤ 3/4000)
    (hn₁ : n₁ ≤ n+t) (hn₂ : n₂ ≤ n+t)
    (hz : z ≤ localCapacity n t) :
    (41/100 ≤ n₁ ∧ n₁ ≤ 423/1000 ∧
     41/100 ≤ n₂ ∧ n₂ ≤ 423/1000 ∧
     17/500 ≤ z ∧ z ≤ 37/1000 ∧
     (n₁+n₂+z ≤ 881/1000 ∧ n₁+n₂+(9/2)*z ≤ 10037/10000)) ∨
    n₁+n₂+(9/2)*z ≤ 1999/2000 := by
  obtain ⟨_,hnt,hcl,hcu,hce,hvolume⟩ := local_capacity_window hn ht htop
  have hn₁' : n₁ ≤ 423/1000 := by linarith
  have hn₂' : n₂ ≤ 423/1000 := by linarith
  have hz' : z ≤ 37/1000 := by linarith
  by_cases hsmall : z ≤ 17/500
  · right
    have hh := old_capacity_of_short hn₁' hn₂' hsmall
    linarith
  · by_cases hdown : n₁ ≤ 41/100 ∨ n₂ ≤ 41/100
    · exact Or.inr (old_capacity_of_downward hn₁' hn₂' hz' hdown)
    · left
      push_neg at hdown
      exact ⟨hdown.1.le,hn₁',hdown.2.le,hn₂',(lt_of_not_ge hsmall).le,hz',
        local_capacity_region hn ht htop hn₁ hn₂ hz⟩

theorem old_capacity_feasible_or_zero {n t z : ℝ} (hz0 : 0 ≤ z)
    (hz : z ≤ oldCapacity n t) :
    2*(n+t)+(9/2)*z ≤ 1 ∨ z=0 := by
  by_cases hraw : 0 ≤ (1-2*(n+t))/(9/2:ℝ)
  · left
    rw [oldCapacity,max_eq_right hraw] at hz
    linarith
  · right
    rw [oldCapacity,max_eq_left (le_of_not_ge hraw)] at hz
    linarith

theorem transport_pair_dispatch {n t n₁ n₂ z : ℝ}
    (hn : BareWindow n) (ht : 0 ≤ t) (hz0 : 0 ≤ z)
    (hn₁ : n₁ ≤ n+t) (hn₂ : n₂ ≤ n+t)
    (hz : z ≤ transportCapacity n t) :
    (41/100 ≤ n₁ ∧ n₁ ≤ 423/1000 ∧
     41/100 ≤ n₂ ∧ n₂ ≤ 423/1000 ∧
     17/500 ≤ z ∧ z ≤ 37/1000 ∧
     (n₁+n₂+z ≤ 881/1000 ∧ n₁+n₂+(9/2)*z ≤ 10037/10000)) ∨
    n₁+n₂+(9/2)*z ≤ 1 ∨ z=0 := by
  by_cases hs : t ≤ 3/4000
  · rw [transportCapacity, if_pos hs] at hz
    rcases local_or_old_pair hn ht hs hn₁ hn₂ hz with hlocal | hold
    · exact Or.inl hlocal
    · exact Or.inr (Or.inl (by linarith))
  · rw [transportCapacity, if_neg hs] at hz
    rcases old_capacity_feasible_or_zero hz0 hz with hold | hzero
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr hzero)

end Local44.Physical
end
/- END ORIGINAL MODULE Physical.Capacity -/

/- BEGIN ORIGINAL MODULE ZetaZeroFree.Analytic.Moments.Plain ; sha256 ab218eb08b3768ee013dba05940570ec7ad10ba4e2d9c5f0a14c836e1cca49df -/
section


namespace ZetaZeroFree.Analytic.Moments

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentRadialEligibleEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def naturalPlainCharacter (η : Character) (z : O) : Character :=
  if hz : z ≠ 0 then (naturalRow η z hz).character else η

/-- The unmarked induction state admits fixed nonprincipal inducing rows.
Displayed moving zeros stay in the character modulus even when their exponent vanishes. -/
structure NaturalPlainState (Z B bΦ Cfixed : ℝ) where
  character : Character
  puncture : Ideal O
  radial : Radial
  rowWidth : ℝ
  characterWidth : ℝ
  displayedSupport : Ideal O
  displayed_squarefree : Squarefree displayedSupport
  displayed_bound : (displayedSupport.absNorm : ℝ) ≤ Z ^ characterWidth
  displayed_zeros : character.modulus ≤ displayedSupport
  base_ge_one : 1 ≤ Z
  row_nonneg : 0 ≤ rowWidth
  character_nonneg : 0 ≤ characterWidth
  scale_eq : radial.scale = Z ^ rowWidth
  modulus_bound : (character.modulus.absNorm : ℝ) ≤ Cfixed * Z ^ characterWidth
  puncture_ne_zero : puncture ≠ 0
  puncture_bound : (puncture.radical.absNorm : ℝ) ≤ Z ^ B
  radial_support : Function.support (radial.profile : ℝ → ℂ) ⊆ Set.Iic bΦ
  row_ne_zero : ∀ z, radial.keep z → z ≠ 0
  row_nonprincipal : ∀ z, radial.keep z → (naturalPlainCharacter character z).residue ≠ 1

namespace NaturalPlainState
variable {Z B bΦ Cfixed : ℝ}

def width (s : NaturalPlainState Z B bΦ Cfixed) : ℝ := s.rowWidth + s.characterWidth

def energy (s : NaturalPlainState Z B bΦ Cfixed)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (X₁ X₂ t₁ t₂ : ℝ) : ℝ :=
  radialEnergy (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false W₁ X₁ 0 t₁ *
    polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false W₂ X₂ 0 t₂) s.radial.keep s.radial.profile s.radial.scale

def restrictLive (s : NaturalPlainState Z B bΦ Cfixed) : NaturalPlainState Z B bΦ Cfixed :=
  { s with
    radial := { s.radial with
      keep := fun z => s.radial.keep z ∧
        s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) ≠ 0 }
    row_ne_zero := fun z hk => s.row_ne_zero z hk.1
    row_nonprincipal := fun z hk => s.row_nonprincipal z hk.1 }

lemma energy_restrictLive (s : NaturalPlainState Z B bΦ Cfixed)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (X₁ X₂ t₁ t₂ : ℝ) :
    s.restrictLive.energy W₁ W₂ X₁ X₂ t₁ t₂ = s.energy W₁ W₂ X₁ X₂ t₁ t₂ := by
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : s.radial.keep z
  · by_cases hp : s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) = 0
    · simp [restrictLive, hk, hp]
    · simp [restrictLive, hk, hp]
  · simp [restrictLive, hk]

end NaturalPlainState

/-- The zero-slot mixed moment contract with uniform smooth and height orders.
The unconditional endpoint is proved in `Moments.Unconditional`. -/
def ZeroOnlyAt (a b bΦ B Cfixed L M ε Z : ℝ) (J : ℕ)
    (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalPlainState Z B bΦ Cfixed, s.width ≤ M →
  ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
    Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
  ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤ C * diagonalControl s.radial.profile *
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
       (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

theorem mixed_height_profile_control (a b : ℝ) (ha : 0 < a) (S : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ))
        (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
        (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b) (t₁ t₂ : ℝ),
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂))) ^ 2 ≤
          C * ((T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
               (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
            (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J := by
  obtain ⟨n, T, C, hC, he⟩ := normPowerProfile_source_control a b ha S
  refine ⟨2 * n, T, C ^ 4, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ t₁ t₂
  have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    (mul_le_mul (he W₁ hs₁ t₁) (he W₂ hs₂ t₂) (apply_nonneg _ _) (by positivity)) 2
  apply hh.trans_eq
  simp only [mul_pow, ← pow_mul, Nat.mul_comm n 2]
  ring

lemma mixed_height_energy_eq (a b : ℝ) (ha : 0 < a) (χ : O → Character)
    (r : Radial) (R : Ideal O) (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b) (X₁ X₂ t₁ t₂ : ℝ) :
    radialEnergy (fun z => polynomial (excluded (χ z) R) false
        (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁) X₁ 0 0 *
      polynomial (excluded (χ z) R) false
        (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) X₂ 0 0) r.keep r.profile r.scale =
    radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 t₁ *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 t₂) r.keep r.profile r.scale := by
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial]

/-- An unconditional width floor. The puncture budget is separate from effective width,
and the row condition includes nonprincipal characters of fixed conductor. -/
theorem mixed_width_floor (a b ε B ρ : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ : O → Character) (r : Radial) (R : Ideal O) (Z m q Q X₁ X₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → 0 ≤ q → 0 ≤ Q → r.scale = Z ^ m →
        m + q ≤ ρ → (R.radical.absNorm : ℝ) ≤ Z ^ B →
        (∀ z, r.keep z → (χ z).residue ≠ 1) →
        (∀ z, r.keep z → ((χ z).modulus.absNorm : ℝ) ≤ Q * Z ^ (m + q)) →
        0 < X₁ → 0 < X₂ →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
          C * Q ^ 4 * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 * Z ^ (m + q + 4 * ρ + ε) := by
  let η : ℝ := ε / (B + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hBη : B * η ≤ ε := by
    have he : η * (B + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  obtain ⟨S, C, hC, he⟩ := CenteredMomentNaturalMaskedFloor.excluded_pair a b η ha hb hη
  refine ⟨S, C, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Z m q Q X₁ X₂ hR hZ hm hq hQ hscale hρ hmask hχ hmod hX₁ hX₂
  have hh := he W₁ W₂ hs₁ hs₂ χ r R (Q * Z ^ (m + q)) X₁ X₂ hR
    (by positivity) hX₁ hX₂ hχ hmod
  rw [hscale, max_eq_right (Real.one_le_rpow hZ hm)] at hh
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hd := diagonalControl_nonneg r.profile
  have hmask' : (R.radical.absNorm : ℝ) ^ η ≤ Z ^ ε := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hmask hη.le).trans
    rw [← Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hBη
  have hp : Z ^ m * (Z ^ (m + q)) ^ 4 ≤ Z ^ (m + q + 4 * ρ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  rw [hscale]
  apply hh.trans
  calc
    _ = (C * Q ^ 4 * diagonalControl r.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2) *
        ((R.radical.absNorm : ℝ) ^ η * (Z ^ m * (Z ^ (m + q)) ^ 4)) := by ring
    _ ≤ (C * Q ^ 4 * diagonalControl r.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2) *
        (Z ^ ε * Z ^ (m + q + 4 * ρ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hmask' hp (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hz]; ring

theorem mixed_width_floor_height (a b ε B ρ : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ : O → Character) (r : Radial) (R : Ideal O) (Z m q Q X₁ X₂ t₁ t₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → 0 ≤ q → 0 ≤ Q → r.scale = Z ^ m →
        m + q ≤ ρ → (R.radical.absNorm : ℝ) ≤ Z ^ B →
        (∀ z, r.keep z → (χ z).residue ≠ 1) →
        (∀ z, r.keep z → ((χ z).modulus.absNorm : ℝ) ≤ Q * Z ^ (m + q)) →
        0 < X₁ → 0 < X₂ →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 t₁ *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 t₂) r.keep r.profile r.scale ≤
          C * Q ^ 4 * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
            (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + 4 * ρ + ε) := by
  obtain ⟨S₀, C₀, hC₀, he⟩ := mixed_width_floor a b ε B ρ ha hb hε hB
  obtain ⟨J, S, C₁, hC₁, hheight⟩ := mixed_height_profile_control a b ha S₀
  refine ⟨J, S, C₀ * C₁, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Z m q Q X₁ X₂ t₁ t₂ hR hZ hm hq hQ hscale hρ hmask hχ hmod hX₁ hX₂
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hsV₁ : Function.support (V₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (CenteredMomentTwist.normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
  have hsV₂ : Function.support (V₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (CenteredMomentTwist.normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂
  have hh := he V₁ V₂ hsV₁ hsV₂ χ r R Z m q Q X₁ X₂ hR hZ hm hq hQ hscale hρ hmask hχ hmod hX₁ hX₂
  rw [mixed_height_energy_eq a b ha χ r R W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂] at hh
  have hd := diagonalControl_nonneg r.profile
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hheight W₁ W₂ hs₁ hs₂ t₁ t₂)
      (by positivity : 0 ≤ C₀ * Q ^ 4 * diagonalControl r.profile))
    (Real.rpow_nonneg (zero_le_one.trans hZ) _)).trans_eq
  ring

theorem zero_only_floor (a b bΦ B Cfixed L ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hbΦ : 0 < bΦ) (hB : 0 ≤ B) (hfixed : 0 < Cfixed) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, ZeroOnlyAt a b bΦ B Cfixed L (ε / 8) ε Z J S C := by
  obtain ⟨J, S, C₀, hC₀, he⟩ := mixed_width_floor_height a b (ε / 2) B (ε / 8)
    ha hb (by positivity) hB
  let F : ℝ := fixedConductorFactor
  have hF : 0 < F := by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0)))
  let Q : ℝ := Cfixed * F * bΦ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨J, S, C₀ * Q ^ 4, by positivity, ?_⟩
  intro Z s hwidth W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ _ _
  let r : Radial := { s.radial with keep := fun z => s.radial.keep z ∧
      (s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) ≠ 0) }
  have hmod (z : O) (hk : r.keep z) :
      ((naturalPlainCharacter s.character z).modulus.absNorm : ℝ) ≤ Q * Z ^ (s.rowWidth + s.characterWidth) := by
    have hz := s.row_ne_zero z hk.1
    have hzn : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ * Z ^ s.rowWidth := by
      rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
      exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hk.2)
    have hh : ((naturalRow s.character z hz).character.modulus.absNorm : ℝ) ≤
        (s.character.modulus.absNorm : ℝ) * F * ((Ideal.span {z}).absNorm : ℝ) := by
      dsimp [F]
      exact_mod_cast (naturalRow s.character z hz).natural_modulus_bound
    simp only [naturalPlainCharacter, dite_eq_left hz]
    apply hh.trans
    calc
      _ ≤ (Cfixed * Z ^ s.characterWidth) * F * (bΦ * Z ^ s.rowWidth) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right s.modulus_bound hF.le) hzn
          (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hfixed.le
            (Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _)) hF.le)
      _ = _ := by dsimp [Q]; rw [Real.rpow_add (zero_lt_one.trans_le s.base_ge_one)]; ring
  have hh := he W₁ W₂ hs₁ hs₂ (naturalPlainCharacter s.character) r s.puncture
    Z s.rowWidth s.characterWidth Q X₁ X₂ t₁ t₂ s.puncture_ne_zero s.base_ge_one
    s.row_nonneg s.character_nonneg hQ.le s.scale_eq hwidth s.puncture_bound
    (fun z hz => s.row_nonprincipal z hz.1) hmod hX₁ hX₂
  have hid : s.energy W₁ W₂ X₁ X₂ t₁ t₂ = radialEnergy
      (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture) false W₁ X₁ 0 t₁ *
        polynomial (excluded (naturalPlainCharacter s.character z) s.puncture) false W₂ X₂ 0 t₂)
      r.keep r.profile r.scale := by
    unfold NaturalPlainState.energy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : s.radial.keep z
    · by_cases hp : s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) = 0
      · simp [r, hk, hp]
      · simp [r, hk, hp]
    · simp [r, hk]
  rw [hid]
  have hex : s.rowWidth + s.characterWidth + 4 * (ε / 8) + ε / 2 = s.width + ε := by
    dsimp [NaturalPlainState.width]
    ring
  rw [hex] at hh
  exact hh

end
end ZetaZeroFree.Analytic.Moments
end
/- END ORIGINAL MODULE ZetaZeroFree.Analytic.Moments.Plain -/

/- BEGIN ORIGINAL MODULE Analytic.JointActiveErrors ; sha256 745a2acfa38a0b6cd0e7cebc40de36fc3b9a2fe614fceef2b99af444801b85b0 -/
section



/-! Removing zero prime-profile entries preserves the extracted errors. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentFirstAmplificationChoice.OriginalData
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationEnergy
open CenteredMomentGaussEnergy CenteredMomentRemainingBox
open CenteredMomentHeckeExpansion
open Local44.Analytic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance activeErrorDecEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem active_amplificationError (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (h p : O) (k : ℕ) :
    amplificationError Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T)
      (fun I => multiplicity p (sourceGenerator D.active.columns I)) p k h =
    amplificationError Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T)
      (fun I => multiplicity p (sourceGenerator D.columns I)) p k h := by
  unfold coefficient
  rw [D.active_beta]
  rw [source_amplificationError D.active.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) p k h,
    source_amplificationError D.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) p k h]
  apply Finset.sum_subset (Finset.filter_subset_filter _ D.active_columns_subset)
  intro I hI hn
  have hz : D.beta I=0 := by
    by_contra hne
    have hm := finite_column_mem (Fintype.piFinset D.active.S) D.active.profile I
      (by change D.active.beta I≠0; rw [D.active_beta]; exact hne)
    exact hn (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hI).2⟩)
  rw [hz,zero_mul,mul_zero,zero_mul]

theorem active_errorEnergy (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (h p : O) :
    errorEnergy Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) h p =
    errorEnergy Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) h p := by
  unfold errorEnergy
  simp_rw [D.active_amplificationError]

#print axioms active_amplificationError
#print axioms active_errorEnergy
end SevenEighths.CenteredMomentFirstAmplificationChoice.OriginalData
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointActiveErrors -/
