import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.Decomposition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic
open Filter HeckeFamily ConcreteTraceCRT CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentFirstReferenceSource
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentFirstScale
open CenteredMomentFirstSourceConductorCaps CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFirstPhysicalLedger
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- An exact dyadic ratio index, independent of any first-label envelope. -/
def sourceRatioIndex (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) : ℤ :=
  (q.2.2 0).val+(q.2.2 1).val-(q.2.2 2).val-(q.2.2 3).val

def sourceRatioBins (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) : Finset ℤ :=
  Finset.univ.image (sourceRatioIndex s R seed K Z ξ)

abbrev SourceRatioFiber (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (r : ℤ) :=
  {q : FirstSourceCoordinate s R seed K Z ξ // sourceRatioIndex s R seed K Z ξ q=r}

omit [DecidableEq ι] in
lemma actual_source_ratio (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) :
    dyadicScale (q.2.2 0)*dyadicScale (q.2.2 1)/
      (dyadicScale (q.2.2 2)*dyadicScale (q.2.2 3)) =
      dyadicScale (sourceRatioIndex s R seed K Z ξ q) := by
  simp only [sourceRatioIndex,dyadicScale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),
    zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  ring

omit [DecidableEq ι] in
lemma actual_source_ratio_fiber (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (r : ℤ) (q : SourceRatioFiber s R seed K Z ξ r) :
    dyadicScale (q.val.2.2 0)*dyadicScale (q.val.2.2 1)/
      (dyadicScale (q.val.2.2 2)*dyadicScale (q.val.2.2 3)) = dyadicScale r := by
  rw [actual_source_ratio,q.property]

/-- Exact physical mass as a sum of norms of full first-label ratio groups.
Every phase has norm at most one; all first labels remain inside each fiber. -/
theorem actual_physical_mass_ratio_groups (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ =
    ∑r∈sourceRatioBins s R seed K Z ξ,
      ‖∑q : SourceRatioFiber s R seed K Z ξ r,
        normPhase (coordinateBlock s R seed W K Z ξ q.val)*
          coordinateBlock s R seed W K Z ξ q.val‖ := by
  rw [actual_physical_mass_joint_sum]
  simp_rw [normPhase_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  simp_rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun q (hq : q∈(Finset.univ : Finset (FirstSourceCoordinate s R seed K Z ξ))) =>
      Finset.mem_image_of_mem (sourceRatioIndex s R seed K Z ξ) hq)]
  apply Finset.sum_congr rfl
  intro r _
  exact (Finset.sum_subtype (Finset.univ.filter (fun q : FirstSourceCoordinate s R seed K Z ξ =>
    sourceRatioIndex s R seed K Z ξ q=r))
    (fun q => by simp) (fun q => ‖coordinateBlock s R seed W K Z ξ q‖))

omit [DecidableEq ι] in
/-- The active and inactive conductor factors give an actual common interval
for the first dyadic center, even as the first labels vary. -/
lemma actual_effective_scale_bounds (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hK : 0<K) (hZ : 1≤Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0)
    (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (q : FirstSourceCoordinate s R seed K Z ξ) :
    K/Z^(2*B)≤effectiveScale q.1.val.1 q.1.val.2 q.2.1.val K ∧
      effectiveScale q.1.val.1 q.1.val.2 q.2.1.val K≤K := by
  let C := q.1.val.1
  let D := q.1.val.2
  let E := q.2.1.val
  have hg := actual_common_gates s R seed hs hz₁ hz₂ C D q.1.property
  have hc : Supported C :=
    (CenteredMomentSecondRetainedAggregate.commonLabels_supported
      (CenteredMomentActiveSource.activeSource (CenteredMomentSourceMass.finiteColumns
        (Fintype.piFinset s.pools)) (coefficient s R seed)) _ _ q.1.property).1
  have hf := original_factor_caps C D hc E
  let e := ‖eisEmbedding (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)‖^2
  let r := ‖eisEmbedding (activeConductor C D)‖^2
  have he1 : 1≤e := by
    rw [show e=((Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}).absNorm:ℝ) by
      exact eisEmbedding_norm_sq_eq_absNorm_span _]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (subsetGenerator_supported C D hc E).1)
  have hr1 : 1≤r := by
    rw [show r=((Ideal.span {activeConductor C D}).absNorm:ℝ) by
      exact eisEmbedding_norm_sq_eq_absNorm_span _]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (finitePrimeModulus_ne_zero _)))
  have he : e≤Z^B := hf.1.trans (hg.2.2.2.2.2.1.trans hsource)
  have hr : r≤Z^B := hf.2.trans (hg.2.2.2.2.2.1.trans hsource)
  have hep : 0<e := zero_lt_one.trans_le he1
  have hrp : 0<r := zero_lt_one.trans_le hr1
  have hz : 0<Z := zero_lt_one.trans_le hZ
  change K/Z^(2*B)≤(K/e)/r ∧ (K/e)/r≤K
  rw [div_div]
  constructor
  · apply div_le_div_of_nonneg_left hK.le (mul_pos hep hrp)
    have hmul := mul_le_mul he hr hrp.le (Real.rpow_nonneg hz.le _)
    simpa only [←Real.rpow_add hz,show B+B=2*B by ring] using hmul
  · exact div_le_self hK.le (one_le_mul_of_one_le_of_one_le he1 hr1)

/-- The common dyadic box contains the dyads of every actual source label.
Its size is logarithmic in scale ratios, never in the number of first labels. -/
abbrev SourceDyadicEnvelope (K Z B L : ℝ) :=
  ∀i : Fin 4,↥(indices (![K/Z^(2*B),1,1,1] i) (![K,Z^L,Z^B,Z^B] i))

omit [DecidableEq ι] in
lemma actual_dyads_in_envelope (s : Input ι) (R seed : Ideal O) (K Z ξ A D B : ℝ)
    (hK : 0<K) (hZ : 1≤Z) (hB : 0≤B)
    (hA : 0≤A) (_hD : 0≤D) (hξ : 0≤ξ)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : 0<sourceRadius s) (hsourcecap : sourceRadius s≤Z^B)
    (hV : CenteredMomentAmplificationChildInput.volume s≤Z^A) (hKi : K⁻¹≤Z^D)
    (q : FirstSourceCoordinate s R seed K Z ξ) (i : Fin 4) :
    (q.2.2 i).val∈indices (![K/Z^(2*B),1,1,1] i)
      (![K,Z^(3*max A D+ξ/2),Z^B,Z^B] i) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hbpow : 1≤Z^B := Real.one_le_rpow hZ hB
  have hf := actual_effective_scale_bounds s R seed K Z ξ B hK hZ hs hz₁ hz₂ hsourcecap q
  have hg := actual_common_gates s R seed hs hz₁ hz₂ q.1.val.1 q.1.val.2 q.1.property
  have hnC : (1:ℝ)≤q.1.val.1.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hg.1)
  have hnD : (1:ℝ)≤q.1.val.2.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hg.2.1)
  fin_cases i
  · apply (mem_indices_iff_scale _ _ (div_pos hK (Real.rpow_pos_of_pos hz _)) hK _).mpr
    have hn := (mem_indices_iff_scale _ _
      (effectiveScale_pos _ _ _ K hK) (effectiveScale_pos _ _ _ K hK) _).mp (q.2.2 0).property
    exact ⟨hf.1.trans hn.1,hn.2.trans (by linarith [hf.2])⟩
  · have hr := local_frequency_radius_cap q.1.val.1 q.1.val.2 q.2.1.val
      K (CenteredMomentAmplificationChildInput.volume s) Z (max A D) ξ hK
      (CenteredMomentAmplificationChildInput.volume_pos s).le hZ
      (hV.trans (Real.rpow_le_rpow_of_exponent_le hZ (le_max_left _ _)))
      (hKi.trans (Real.rpow_le_rpow_of_exponent_le hZ (le_max_right _ _)))
    obtain ⟨hret,a,ha,hne⟩ := (mem_retainedIndices _ _).mp (q.2.2 1).property
    have hi := retained_integral_mem _ a ha _ hret hne
    apply indices_mono_upper _ _ _ (by norm_num) (by positivity) _ hi
    apply max_le (Real.one_le_rpow hZ (by
      have hm : 0≤max A D := hA.trans (le_max_left _ _)
      positivity)) hr
  · exact indices_mono_upper _ _ _ (by norm_num)
      (div_pos hsource (zero_lt_one.trans_le hnC))
      ((div_le_self hsource.le hnC).trans hsourcecap) (q.2.2 2).property
  · exact indices_mono_upper _ _ _ (by norm_num)
      (div_pos hsource (zero_lt_one.trans_le hnD))
      ((div_le_self hsource.le hnD).trans hsourcecap) (q.2.2 3).property

/-- A single common four-dimensional dyadic box has a uniform small-power
size. Its first interval is centered at the one global physical scale K. -/
theorem source_dyadic_envelope_subpower (B L ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀K : ℝ,0<K →
      (Fintype.card (SourceDyadicEnvelope K Z B L):ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower 1 (3*B+L) ε (by norm_num)
    (by positivity) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hz hZ
  intro K hK
  have hp : 0<Z := zero_lt_one.trans_le hZ
  have hb : 1≤Z^B := Real.one_le_rpow hZ hB
  have hbb : 1≤Z^(2*B) := Real.one_le_rpow hZ (by positivity)
  have hl : 1≤Z^L := Real.one_le_rpow hZ hL
  apply hz ![K/Z^(2*B),1,1,1] ![K,Z^L,Z^B,Z^B]
  · intro i; fin_cases i
    · change 0<K/Z^(2*B); positivity
    · change (0:ℝ)<1; norm_num
    · change (0:ℝ)<1; norm_num
    · change (0:ℝ)<1; norm_num
  · intro i; fin_cases i
    · change K/Z^(2*B)≤K; exact div_le_self hK.le hbb
    · change 1≤Z^L; exact hl
    · change 1≤Z^B; exact hb
    · change 1≤Z^B; exact hb
  · intro i; fin_cases i
    · change K/(K/Z^(2*B))≤1*Z^(3*B+L)
      have he : K/(K/Z^(2*B))=Z^(2*B) := by field_simp
      rw [he,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · change Z^L/1≤1*Z^(3*B+L)
      rw [div_one,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · change Z^B/1≤1*Z^(3*B+L)
      rw [div_one,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · change Z^B/1≤1*Z^(3*B+L)
      rw [div_one,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

omit [DecidableEq ι] in
/-- Counting the image of actual dyadic tuples costs no first-label count.
The uniform box includes every original physical-mass coordinate. -/
theorem actual_ratio_bins_subpower (A D B ξ ε : ℝ)
    (hA : 0≤A) (hD : 0≤D) (hB : 0≤B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ),0<K →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B →
      CenteredMomentAmplificationChildInput.volume s≤Z^A → K⁻¹≤Z^D →
      ((sourceRatioBins s R seed K Z ξ).card:ℝ)≤C*Z^ε := by
  let L := 3*max A D+ξ/2
  have hL : 0≤L := by dsimp [L]; have hm := hA.trans (le_max_left A D); positivity
  obtain ⟨C,hC,hcount⟩ := source_dyadic_envelope_subpower B L ε hB hL hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro s R seed K hK hs hz₁ hz₂ hsource hsourcecap hV hKi
  let index : SourceDyadicEnvelope K Z B L→ℤ := fun n =>
    (n 0).val+(n 1).val-(n 2).val-(n 3).val
  have hsub : sourceRatioBins s R seed K Z ξ⊆Finset.univ.image index := by
    intro r hr
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
    let n : SourceDyadicEnvelope K Z B L := fun i =>
      ⟨(q.2.2 i).val,actual_dyads_in_envelope s R seed K Z ξ A D B hK hZ hB
        hA hD hξ hs hz₁ hz₂ hsource hsourcecap hV hKi q i⟩
    exact Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩
  have hcard : (sourceRatioBins s R seed K Z ξ).card≤
      Fintype.card (SourceDyadicEnvelope K Z B L) :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  exact (show ((sourceRatioBins s R seed K Z ξ).card:ℝ)≤
      Fintype.card (SourceDyadicEnvelope K Z B L) by exact_mod_cast hcard).trans (hcount K hK)

omit [DecidableEq ι] in
/-- Coherent ratio loss for actual physical mass: an arbitrary natural decay
power introduces at most the same uniform small-power overhead. -/
theorem actual_ratio_decay_sum_subpower (A D B ξ ε : ℝ)
    (hA : 0≤A) (hD : 0≤D) (hB : 0≤B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ),0<K →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B →
      CenteredMomentAmplificationChildInput.volume s≤Z^A → K⁻¹≤Z^D →
      ∀N : ℕ,∑r∈sourceRatioBins s R seed K Z ξ,(1+dyadicScale r)^(-(N:ℝ))≤C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := actual_ratio_bins_subpower (ι:=ι) A D B ξ ε hA hD hB hξ hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hcount
  intro s R seed K hK hs hz₁ hz₂ hsource hsourcecap hV hKi N
  apply (Finset.sum_le_sum (fun r _ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [dyadicScale_pos r])
      (neg_nonpos.mpr (Nat.cast_nonneg N)))).trans
  simpa using hcount s R seed K hK hs hz₁ hz₂ hsource hsourcecap hV hKi

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_source_ratio_fiber
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_ratio_groups
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_effective_scale_bounds
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_dyads_in_envelope
#print axioms OAI.SevenEighths.Cycle61InitialMass.source_dyadic_envelope_subpower
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_ratio_bins_subpower
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_ratio_decay_sum_subpower
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_ratio_groups,
      ``OAI.SevenEighths.Cycle61InitialMass.actual_ratio_bins_subpower,
      ``OAI.SevenEighths.Cycle61InitialMass.actual_ratio_decay_sum_subpower] do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut idx := 0
    let mut denied : Array Name := #[]
    let mut missing : Array Name := #[]
    while idx < todo.size do
      let n := todo[idx]!
      idx := idx+1
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``sorryAx || #["ColumnBounds", "actual_reference_block", "original_block_sum",
          "CenteredMomentEnergyOriginalHighReflectionPower", "Cycle61Moment.InitialAffineAt",
          "Cycle61.Assembly.Final", "PositiveHighSourceBound"].any
          (fun ban => (n.toString.splitOn ban).length>1) then
        denied := denied.push n
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          if #["OAI.", "Cycle25.", "Cycle61.", "ZetaZeroFree.",
              "_private.OAI.", "_private.Cycle25.", "_private.Cycle61.",
              "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
            todo := todo.push dep
    let required := if root == ``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_ratio_groups
      then #[``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_joint_sum]
      else #[``OAI.SevenEighths.CenteredMomentOriginalCommonHarmonic.actual_common_gates,
        ``OAI.SevenEighths.CenteredMomentFirstSourceConductorCaps.original_factor_caps,
        ``OAI.SevenEighths.CenteredMomentFirstPhysicalDyadicCount.local_frequency_radius_cap,
        ``OAI.SevenEighths.CenteredMomentDyadicCount.four_indices_subpower]
    for n in required do
      unless seen.contains n do throwError "Genuine source ratio dependency missing: {n}"
    logInfo m!"{root}: {seen.size} project constants; denied={denied}; missing={missing}"
    unless denied.isEmpty && missing.isEmpty do throwError "Actual ratio-bin audit rejected"
