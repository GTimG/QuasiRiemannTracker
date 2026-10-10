import WeightedQRH.HighRows.WeightedSourceFinish

/-! Arithmetic and detector hypotheses for the literal retained full-w cells. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.WeightedHighFinalAssembly
open ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification

/-- The nonzero physical source normalizer already implies that every actual
prime slot has a label.  No separate prime-distribution input is required. -/
theorem weighted_source_pools_nonempty {Δ : ℝ}
    (D : WeightedQRH.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∀ᶠZ : ℝ in atTop,∀j : Fin D.N,(WeightedQRH.Numerator.sourcePrimePool F Z j).Nonempty := by
  obtain ⟨C,hC,hbound⟩ := weighted_source_normalizer_bound D F
  filter_upwards [hbound] with Z hn
  intro j
  by_contra hne
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
  have hmass : PrincipalSignalComparison.slotMass (WeightedQRH.Numerator.sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) (fun j=>Z^(D.ell j))) j=0 := by
    simp only [PrincipalSignalComparison.slotMass,hempty,Finset.sum_empty]
  have hprod : (∏i : Fin D.N,PrincipalSignalComparison.slotMass
      (WeightedQRH.Numerator.sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) (fun j=>Z^(D.ell j))) i)=0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hmass
  apply hn.1
  unfold weightedSourceNormalizer Probe.principalScalar
  exact mul_eq_zero_of_right _ (Complex.ofReal_eq_zero.mpr (mul_eq_zero_of_right _ hprod))

/-- A source-conductor threshold can be chosen uniformly for all dyads in a
fixed positive exponent range. -/
theorem eventually_uniform_source_conductor {P : ℝ→Prop} (dmin : ℝ) (hdmin : 0 < dmin)
    (hP : ∀ᶠU : ℝ in atTop,P U) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin ≤ d → P (Z^d) := by
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hP
  filter_upwards [(tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U0),
    eventually_ge_atTop (1:ℝ)] with Z hZmin hZ
  intro d hd
  exact hU0 (Z^d) (hZmin.trans (Real.rpow_le_rpow_of_exponent_le hZ hd))

/-- The actual external rectangle is within the bounded-height source count
range, after a threshold depending only on the finite height index budget. -/
theorem weighted_source_height_le (τ : ℝ) (n : ℕ) (hτ : 0 < τ) :
    ∀ᶠZ : ℝ in atTop,∀i : ℕ,i ≤ n →
      0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ ∧ ((3*i+1:ℕ):ℝ)*Z^τ ≤ Z^(2*τ) := by
  filter_upwards [HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hn hZ
  intro i hi
  have hi' : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hZp : 0 < Z := zero_lt_one.trans hZ
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ (3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
    _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring

def weightedCellRows {Δ : ℝ} (D : WeightedQRH.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z : ℝ) (idx grid : FreeRow→ℕ)
    (k i j : ℕ) : Finset FreeRow :=
  cubeBinRows ((supportedNonfloorRows F.S F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^((1587/2000:ℝ)+D.t))) grid)∩dyadicRows 1 k)
    idx grid i j

structure WeightedCellRowData {Δ : ℝ} (D : WeightedQRH.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character) (Z τ : ℝ)
    (idx grid : FreeRow→ℕ) (n k i j : ℕ) : Prop where
  a_lower : (51/100:ℝ) < 51/100+D.e*j
  a_upper : (51/100:ℝ)+D.e*j ≤ 7/8
  d_lower : (1/200:ℝ) ≤ sourceDyadConductor Z D.t k
  d_upper : sourceDyadConductor Z D.t k ≤ 7/8
  index_le : i ≤ n
  rows_source : ∀u∈weightedCellRows D F Z idx grid k i j,
    u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u ≤ Z^(sourceDyadConductor Z D.t k-D.t)
  rows_moment : ∀u∈weightedCellRows D F Z idx grid k i j,
    (Z^(sourceDyadConductor Z D.t k))^(1/100:ℝ) ≤ rowNorm u ∧
      rowNorm u ≤ Z^(sourceDyadConductor Z D.t k)
  rows_nonprincipal : ∀u∈weightedCellRows D F Z idx grid k i j,
    (rowCharacter F.S F.exclusions.prime u).residue≠1
  rows_frequency : ∀u∈weightedCellRows D F Z idx grid k i j,
    Z^(sourceDyadConductor Z D.t k-2*D.t) ≤ rowNorm u
  next : ∀u∈weightedCellRows D F Z idx grid k i j,
    detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(i+1:ℕ)*Z^τ) < 51/100+D.e*j+2*D.e
  current : ∀u∈weightedCellRows D F Z idx grid k i j,
    (51/100:ℝ)+D.e*j ≤ detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*i:ℕ)*Z^τ)

theorem weighted_source_cell_geometry {Δ : ℝ}
    (D : WeightedQRH.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀(η : Character) (τ : ℝ) (n : ℕ) (idx grid : FreeRow→ℕ),
      let rows := supportedNonfloorRows F.S F.maximal
        (rowBand (Z^(1/100:ℝ)) (Z^((1587/2000:ℝ)+D.t))) grid
      (∀u∈rows,idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/D.e⌋₊ ∧
        (51/100:ℝ)+D.e*grid u ≤ 7/8) →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(idx u+1:ℕ)*Z^τ) < 51/100+D.e*grid u+2*D.e) →
      (∀u∈rows,(51/100:ℝ)+D.e*grid u ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*idx u:ℕ)*Z^τ)) →
      ∀k i j : ℕ,i∈Finset.range (n+1) →
        (weightedCellRows D F Z idx grid k i j).Nonempty →
        WeightedCellRowData D F η Z τ idx grid n k i j := by
  have htop : (1587/2000:ℝ)+D.t+2*D.t ≤ 7/8 := by linarith only [D.t_small]
  filter_upwards [sourceDyad_geometry_eventually (1/200) (7/8) D.t (1587/2000+D.t)
    (by norm_num) (by norm_num) D.t_pos htop,eventually_gt_atTop (1:ℝ)] with Z hgeo hZ
  refine ⟨hZ,?_⟩
  intro η τ n idx grid
  dsimp only
  intro hlabels hnext hcurrent k i j hi hne
  let rows := supportedNonfloorRows F.S F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^((1587/2000:ℝ)+D.t))) grid
  let cell := weightedCellRows D F Z idx grid k i j
  have hsub : cell⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : cell⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      rowNorm u ≤ Z^(1587/2000+D.t) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ) < 51/100+D.e*j := by
    have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j ≤ 7/8 := by
    simpa only [huj] using (hlabels u (hsubr hu)).2.2
  have hsource : ∀v∈cell,v.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm v ∧
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
      rowNorm v ≤ Z^(sourceDyadConductor Z D.t k-D.t) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,
      hg.2.2.2.2.2 v (hsub hv)⟩
  refine ⟨ha,ha',hg.2.2.1,hg.2.2.2.1,
    Nat.le_of_lt_succ (Finset.mem_range.mp hi),hsource,?_,?_,?_,?_,?_⟩
  · intro v hv
    constructor
    · apply le_trans _ (hsource v hv).2.1
      rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hg.2.2.2.1])
    · apply (hsource v hv).2.2.2.trans
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [D.t_pos])
  · intro v hv
    exact calibrated_row_nonprincipal F.S F.exclusions.prime F.maximal F.exclusions.bad
      v (hsource v hv).1 (hsource v hv).2.2.1
  · intro v hv
    simpa only [sourceDyadConductor,add_sub_cancel_right] using (hg.2.2.2.2.1 v (hsub hv)).1
  · intro v hv
    have hh := hnext v (hsubr hv)
    have hm := (mem_cubeBinRows _ idx grid i j v).mp hv
    rwa [hm.2.1,hm.2.2] at hh
  · intro v hv
    have hh := hcurrent v (hsubr hv)
    have hm := (mem_cubeBinRows _ idx grid i j v).mp hv
    rwa [hm.2.1,hm.2.2] at hh

end SevenEighths.WeightedHighFinalAssembly
end
end OAI
