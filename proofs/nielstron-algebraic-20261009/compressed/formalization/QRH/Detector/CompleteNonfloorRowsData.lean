import QRH.NumericFacts
import QRH.Detector.CompleteNonfloorCubeData
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

/-! Actual normalized nonfloor central rows after all dyadic and detector-bin
partitions. No moment or central-cube estimate is an input. -/
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHUniformDetectorMoment
open HeckeFamily ProbePhysical ProbeFinalAssembly HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily QRHDynamicMomentInput
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem exists_optimized_nonfloor_rows_bound_with_parameters (gap:ℝ) (hgap:0<gap)
    (hgap1:gap≤(1-QRH.kappa0)/2)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤QRH.kappa0+2*gap)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta):
    ∃D:Parameters.HighData gap,∃S:SourceData D,∃τ:ℝ,0<τ ∧
    τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧
    D.t<gap/100 ∧ 2000*D.ε≤D.t ∧ 2000*D.e≤D.t ∧
    ((D.N:ℝ)+8)*D.eps≤D.t ∧
    (∀j,QRHParameters.optimizedLengths D j≤D.t/200) ∧ τ*(2+4*D.eps)<D.t ∧
    ∀n m:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀rows:Finset FreeRow,
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S.S S.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(QRH.h+D.t))→
    ∀idx grid:FreeRow→ℕ,
    (∀u∈rows,idx u≤n ∧ grid u≤m ∧ grid u≠0 ∧ (51/100:ℝ)+D.e*grid u≤1)→
    (∀u∈rows,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^τ)<51/100+D.e*grid u+2*D.e)→
    (∀u∈rows,51/100+D.e*grid u≤detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
      (rayCubeFamily S.modulus ⊤ le_top u)) ((3*idx u:ℕ)*Z^τ))→
    let Y:Fin D.N→ℝ:=fun j=>Z^(QRHParameters.optimizedLengths D j);
    let T:Fin D.N→Finset ProbePhysical.PrimeIdeal:=fun j=>ProbeRaySlots.pool
      (RayQuotient.identityClass S.modulus ⊤) S.S 1 2 (Y j);
    let hT:∀j P,P∈T j→P.val∉S.S:=fun j P hP=>
      (ProbeRaySlots.mem_pool _ S.S 1 2 (Y j) P).mp hP |>.2.2.2;
    let normer:=PrincipalMellinResidues.sourceResidueConstant S.W S.W S.modulus*
      (Probe.principalScalar Finset.univ Z QRH.ell
        (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights (fun _=>S.w) Y)):ℂ);
    normer≠0 ∧ ‖finiteCentralCubeRows S.S S.exclusions S.maximal η rows T hT
      (fun _ x=>(S.w x:ℂ)) Y S.W S.W (Z^QRH.lx) (Z^QRH.ly) Z D.e
      (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
      C*(η.modulus.absNorm:ℝ)^(2*D.eps)*Z^(QRH.C (QRH.tightTheta+gap)-D.sigma/4) := by
  obtain ⟨D,S,τ,hτ,hτd,hτcost,ht,hε,he,heps,hsmall,hτeps,hcube⟩:=exists_optimized_nonfloor_cube_bound_with_parameters gap hgap hgap1 hκbeta hbeta
  obtain ⟨Cn,hCn,hnormer⟩:=actual_ray_normalizer_inverse_optimized S.modulus ⊤ le_top S.S S.exclusions
    1 2 (by norm_num) (by norm_num) (QRHParameters.optimizedLengths D)
    (QRHParameters.optimizedLengths_pos D) (QRHParameters.optimizedLengths_sum D) (fun _=>S.w)
    (fun _=>S.smooth) (fun _=>S.compact) (fun _=>S.support) (fun _ y=>(S.bounded y).1) (fun _=>S.nonzero)
    S.W S.W 1 2 1 2 (by norm_num) (by norm_num) S.complex_support S.complex_support
    S.real S.real S.nonnegative S.nonnegative S.complex_nonzero S.complex_nonzero (D.sigma/4)
    (by linarith [D.sigma_pos])
  obtain ⟨Cd,hCd,hdyad⟩:=canonical_dyad_cost (D.sigma/4) (by linarith [D.sigma_pos])
  have hepos:=D.e_pos
  have hcap := QRH.NumericFacts.h_sharp_upper
  have hconductor:QRH.h+D.t+2*D.t≤(7/8:ℝ):=by linarith [D.t_small]
  refine ⟨D,S,τ,hτ,hτd,hτcost,ht,hε,he,heps,hsmall,hτeps,?_⟩
  intro n m η
  obtain ⟨C,hC,hbound⟩:=hcube n η
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  filter_upwards [hbound,hnormer,
    sourceDyad_geometry_eventually (1/200) (7/8) D.t (QRH.h+D.t)
      (by norm_num) (by norm_num) D.t_pos hconductor] with Z hb hn hg
  refine ⟨hb.1,?_⟩
  intro rows hrows idx grid hlabels hnext hcurrent Y T hT normer
  refine ⟨hn.1,?_⟩
  have hZ:1<Z:=hb.1
  have hZp:0<Z:=zero_lt_one.trans hZ
  let WC:Fin D.N→ℝ→ℂ:=fun _ x=>(S.w x:ℂ)
  let bound:ℝ:=C*(η.modulus.absNorm:ℝ)^(2*D.eps)*Z^(QRH.C (QRH.tightTheta+gap)-D.sigma/2)
  have hD:0≤bound:=by dsimp [bound];positivity
  let F:Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ:=fun R a H=>
    finiteCentralCubeRows S.S S.exclusions S.maximal η R T hT WC Y S.W S.W
      (Z^QRH.lx) (Z^QRH.ly) Z D.e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(QRH.h+D.t)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+D.e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤bound := by
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
      have ha : 51/100<51/100+D.e*j := by
        have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51/100+D.e*j≤1 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u (rayCubeFamily S.modulus ⊤ le_top u))
          (3*(i+1:ℕ)*Z^τ)<51/100+D.e*j+2*D.e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+D.e*j≤detectorMaximum
          (sourceDetectorFamily S.S S.exclusions.prime η u (rayCubeFamily S.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hbounded := hb.2 (sourceDyadConductor Z D.t k) hgeo.2.2.1 hgeo.2.2.2.1
        (sourceDyadExponent Z k) (51/100+D.e*j) i
        (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hgeo.1 hgeo.2.1
        (by unfold sourceDyadConductor;linarith) ha ha' Rij ⟨u,hu⟩
        (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
        (fun u hu=>hgeo.2.2.2.2.1 u (hsubk hu)) hnext' hcurrent'
      exact hbounded.2
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(QRH.h+D.t)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(QRH.h+D.t)),(n+1:ℕ)*(m+1:ℕ)*bound := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S.S S.exclusions S.maximal η (rows∩dyadicRows 1 k) T hT WC Y
        S.W S.W (Z^QRH.lx) (Z^QRH.ly) Z D.e (Z^τ) idx grid n m
        (fun u hu=>⟨(hlabels u (Finset.mem_inter.mp hu).1).1,(hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
      dsimp only [F]
      rw [hpart,Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),bound := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=>hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(QRH.h+D.t))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*bound) := by simp
    _ ≤ (Cd*Z^(D.sigma/4))*((n+1:ℕ)*(m+1:ℕ)*bound) :=
      mul_le_mul_of_nonneg_right (hdyad Z (QRH.h+D.t) hZ.le (by linarith)) (by positivity)
    _ = _ := by
      dsimp [bound]
      rw [show QRH.C (QRH.tightTheta+gap)-D.sigma/4=
        (QRH.C (QRH.tightTheta+gap)-D.sigma/2)+D.sigma/4 by ring,Real.rpow_add hZp]
      ring

end SevenEighths.QRHUniformDetectorMoment
end
end OAI
