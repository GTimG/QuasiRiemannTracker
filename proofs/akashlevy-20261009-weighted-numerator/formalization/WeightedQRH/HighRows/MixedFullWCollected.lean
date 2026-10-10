import WeightedQRH.HighRows.NonfloorCollected
import WeightedQRH.HighRows.CubeFullWNormalized
import WeightedQRH.LowNormalizer
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyNormalized
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
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

private lemma norm_le_of_fullW_transfer {A B : ℂ} {C P : ℝ}
    (hAB : ‖A-B‖ ≤ 1) (hB : ‖B‖ ≤ C*P) (hP : 1 ≤ P) :
    ‖A‖ ≤ (C+1)*P := by
  calc
    _ = ‖(A-B)+B‖ := by rw [sub_add_cancel]
    _ ≤ ‖A-B‖+‖B‖ := norm_add_le _ _
    _ ≤ 1+C*P := add_le_add hAB hB
    _ ≤ (C+1)*P := by linarith only [hP]

theorem actual_mixed_fullW_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=167/1000)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y ≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (μ top : ℝ) (htop : top ≤ 1)
    (hfinal : (159*ε+εm+R+7*ν)+(12*e+eps*(N+8))+
      (logCost+heightCost+momentCost+loss+mesh*167/1000+(13243/1000)*e)+μ≤1/40000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0 < nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0 < dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : top+2*margin ≤ dmax)
    (hweightedTop : top+2*margin ≤ WeightedQRH.h+WeightedQRH.rowExtension)
    (hmuMargin : 2*margin≤μ) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,1 ≤ C0 → ∀weightedC : ℝ,0 ≤ weightedC → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(top)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u ≤ n ∧ grid u ≤ m ∧ grid u≠0 ∧ 51/100+e*grid u≤7/8) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      -- This is the only new analytic input: actual normalized full-w cells outside the old branch.
      -- It is a premise, not a theorem asserting that the weighted estimate has been proved.
      (∀k∈smallDyadicIndices (Z^top),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        let Y : Fin N→ℝ := fun j=>Z^(ell j)
        let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
        let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
          (Probe.principalScalar Finset.univ Z (167/1000)
            (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
        rows'.Nonempty →
        (1/2:ℝ) < sourceDyadConductor Z margin k →
        (1/3:ℝ) < 2*(51/100+e*j)-1 →
        sourceDyadConductor Z margin k ≤ WeightedQRH.h+WeightedQRH.rowExtension →
        ‖WeightedQRH.FullWContour.finiteCentralFullWRows S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y)
          (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e
          (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖ ≤
          weightedC*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(WeightedQRH.signal WeightedQRH.theta-1/40000+nu)) →
      (∀k∈smallDyadicIndices (Z^(top)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) 0
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (167/1000)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*(2+weightedC)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(WeightedQRH.signal WeightedQRH.theta-1/40000+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ :=
    actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm ν logCost heightCost momentCost hεm hν hlog hMomentHeight
      μ hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu counts
  have hellpos (j : Fin N) : 0 < ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := WeightedLowNormalizer.actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Ct,hCt,htransfer⟩ := actual_normalized_cube_fullW_arbitrary_saving M H hH N τ 1 c b A
    WeightedQRH.rowExtension nu hτ hc hcb hA (by norm_num [WeightedQRH.rowExtension]) hnu
    e he he1 S hS hmax hfirst ell hellpos hell hellsum W hW hcompact hWs hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*(C+1),by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (top) hdmin hdmin1 hmargin hconductor,
    htransfer, source_cube_height_eventually τ hτ,
    eventually_ge_atTop ((Ct+1)*(η.modulus.absNorm:ℝ)^2),
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg ht hheightZ hlargeZ hZ
  intro C0 hC0 weightedC hweightedC rows hrows idx grid hlabels hnext hcurrent hweighted hmom
  have hC0zero : 0 ≤ C0 := zero_le_one.trans hC0
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0 < Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (167/1000)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := (C+1)*(2+weightedC)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(WeightedQRH.signal WeightedQRH.theta-1/40000+nu)
  have hD : 0 ≤ D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(top)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖ ≤ D := by
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
        have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith only [he, hjp]
      have ha' : 51/100+e*j≤7/8 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j ≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      by_cases hbranch : WeightedQRH.OriginalBranch (sourceDyadConductor Z margin k) (51/100+e*j)
      · have hbounded := hb (sourceDyadConductor Z margin k) hgeo.2.2.1 hgeo.2.2.2.1
          (sourceDyadExponent Z k) (51/100+e*j) C0 hgeo.1 (by unfold sourceDyadConductor;linarith)
          (by unfold sourceDyadConductor;linarith) ha ha' hbranch hC0zero Rij
          (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
            (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
          (fun u hu=>hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          hnext' hcurrent' (fun t ht=>hmom k hk i hi j hj ⟨u,hu⟩ t ht)
        apply hbounded.2.trans
        dsimp [D]
        gcongr
        nlinarith only [hC, hweightedC, mul_nonneg hC.le hweightedC]
      · have hdtop' : sourceDyadConductor Z margin k ≤ WeightedQRH.h+WeightedQRH.rowExtension := by
          unfold sourceDyadConductor
          linarith only [hgeo.2.1,hweightedTop]
        have hregime : (1/2:ℝ) < sourceDyadConductor Z margin k ∧
            (1/3:ℝ) < 2*(51/100+e*j)-1 := by
          unfold WeightedQRH.OriginalBranch at hbranch
          constructor
          · by_contra hbad
            exact hbranch ⟨hdtop',Or.inr (le_of_not_gt hbad)⟩
          · by_contra hbad
            exact hbranch ⟨hdtop',Or.inl (le_of_not_gt hbad)⟩
        have hw := hweighted k hk i hi j hj ⟨u,hu⟩ hregime.1 hregime.2 hdtop'
        have htop' : top ≤ (1587:ℝ)/2000+WeightedQRH.rowExtension := by
          change top+2*margin ≤ (1587:ℝ)/2000+WeightedQRH.rowExtension at hweightedTop
          linarith only [hweightedTop,hmargin]
        have hRtop : ∀u∈Rij,u.val≠1 ∧
            ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ≤ Z^((1587:ℝ)/2000+WeightedQRH.rowExtension) := by
          intro u hu
          refine ⟨(hrows u (hsub hu)).1,?_⟩
          exact (hrows u (hsub hu)).2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le htop')
        have hcellData : ∀u∈Rij,(51/100:ℝ) ≤ 51/100+e*j ∧ 51/100+e*j ≤ 1 ∧
            2 < Z^τ ∧ Z^τ ≤ (3*i+1:ℕ)*Z^τ ∧ (3*i+1:ℕ)*Z^τ ≤ (3*i+2:ℕ)*Z^τ ∧
            detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
              (3*(i+1:ℕ)*Z^τ) < 51/100+e*j+2*e := by
          intro u hu
          refine ⟨ha.le,ha'.trans (by norm_num),hheightZ.2,?_,?_,hnext' u hu⟩
          · have hc : (1:ℝ) ≤ (3*i+1:ℕ) := by exact_mod_cast (by omega : 1 ≤ 3*i+1)
            simpa using mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZp.le τ)
          · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 3*i+1 ≤ 3*i+2)) (Real.rpow_nonneg hZp.le τ)
        have herr := (ht η Rij hRtop (fun _=>51/100+e*j) (fun _=>Z^τ)
          (fun _=>(3*i+1:ℕ)*Z^τ) (fun _=>i) hcellData).2
        have hsaving : Ct*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) ≤ 1 := by
          calc
            _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
              (by nlinarith only [hlargeZ,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
            _ = 1 := by rw [Real.rpow_neg_one]; exact mul_inv_cancel₀ hZp.ne'
        have hηone : (1:ℝ) ≤ (η.modulus.absNorm:ℝ)^(2*eps) :=
          Real.one_le_rpow (HeckeLogarithmicInput.modulus_norm_ge_one η) (by positivity)
        have hpone : (1:ℝ) ≤ Z^(WeightedQRH.signal WeightedQRH.theta-1/40000+nu) := by
          apply Real.one_le_rpow hZ.le
          norm_num [WeightedQRH.signal,WeightedQRH.theta,WeightedQRH.b]
          linarith only [hnu]
        have hone : (1:ℝ) ≤ C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(WeightedQRH.signal WeightedQRH.theta-1/40000+nu) :=
          one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC0 hηone) hpone
        have htriangle := norm_le_of_fullW_transfer (C:=weightedC)
          (P:=C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(WeightedQRH.signal WeightedQRH.theta-1/40000+nu))
          (herr.trans hsaving) (by simpa only [mul_assoc] using hw) hone
        simp only [←mul_assoc] at htriangle
        apply htriangle.trans
        dsimp [D]
        gcongr
        nlinarith only [hC,hweightedC,mul_nonneg hC.le hweightedC]
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(top)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(top)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(747/2000:ℝ)) (Z^(919/2000:ℝ)) Z e (Z^τ) idx grid n m
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
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=>hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(top))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (top) hZ.le htop) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (WeightedQRH.signal WeightedQRH.theta-1/40000+nu) dyadCost];ring

end SevenEighths.WeightedHighRowFamily

end

end OAI
