/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B109
import Submissions.cycle61_c0125139.Bundles.B116
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondActualWidth
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondChildCaps; sha256 dc7219af153c91c79fe35867a71cd2e08b43727615c35f217f647f15d458ae4a -/
section
                                                      
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- A supported first common child has a source cap from the original
volume and fixed profile support, uniformly in its character and height. -/
theorem actual_common_child_source_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    sourceRadius (child s C R B χ t)≤ geometry N b bs bs*volume s/(C.absNorm:ℝ) := by
  have hr := (radius_bound N b bs bs hb hbs hbs (child s C R B χ t)
    ((live_card_le B.val).trans hcard) (endpoints_child b bs bs s he C R B χ t)).2
  have hv := common_volume_le N b hb s hcard he.1 C R B χ t hne
  apply hr.trans
  apply (mul_le_mul_of_nonneg_left hv (by positivity : 0≤ b^N*bs*bs)).trans_eq
  unfold geometry
  rw [show 2*N=N+N by omega,pow_add]
  ring

/-- The main-ball correction prevents the second Fourier scale from
exceeding the original physical scale, apart from fixed support factors.
This coarse bound is only used to count dyadic intervals. -/
theorem main_fourier_scale_upper (reflected : Bool)(C D E : Ideal O)
    (hC : C≠0)(hD : D≠0)(hE : E≠0)(heq : primeSupport C=primeSupport D)
    (K V Z sigma delta reserve b : ℝ)(N : ℕ)
    (hK : 0< K)(hV : 0< V)(hZ : 1< Z)(hb : 0< b)
    (hsigma : 0≤ sigma)(hdelta : 0≤ delta)(hreserve : 0≤ reserve) :
    (b^N*V/((if reflected then D else C).absNorm:ℝ))^2/
      mainCommonRadius Z (Real.logb Z ((if reflected then C else D).absNorm:ℝ))
        (nominalLog C D E K V Z)
        (Real.logb Z ((if reflected then D else C).absNorm:ℝ)) sigma delta reserve≤ b^(2*N)*K := by
  have hc := norm_pos C hC
  have hd := norm_pos D hD
  have he := norm_pos E hE
  have hr := active_norm_pos C D
  have hz : 0< Z := zero_lt_one.trans hZ
  have hege : (1:ℝ)≤ E.absNorm := norm_ge_one E hE
  have hrge : (1:ℝ)≤(Ideal.span {activeConductor C D}).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have helog := Real.logb_nonneg hZ hege
  have hrlog := Real.logb_nonneg hZ hrge
  cases reflected <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals
    apply (Real.logb_le_logb hZ (by unfold mainCommonRadius; positivity) (by positivity)).mp
    unfold mainCommonRadius nominalLog
    rw [nominal_equal_support C D E hC hD heq K V]
    simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  · linarith [le_max_left (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)) 0]
  · linarith [le_max_left (Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ)) 0]

/-- Exact Fourier logarithm for either first rectangle. This retains the
six-amplifier saving and cancels the inactive first radical explicitly. -/
theorem main_fourier_frequency_log (reflected : Bool)(C D E : Ideal O)
    (hC : C≠0)(hD : D≠0)(hE : E≠0)(heq : primeSupport C=primeSupport D)
    (K V Z sigma delta reserve ξ b : ℝ)(N : ℕ)
    (hK : 0< K)(hV : 0< V)(hZ : 1< Z)(hb : 0< b) :
    let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
    let R := frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/
      mainCommonRadius Z d (nominalLog C D E K V Z) c sigma delta reserve) Z ξ
    Real.logb Z R+Real.logb Z (E.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      Real.logb Z K-max (c-d) 0-2*sigma-delta-reserve+
        2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hc := norm_pos C hC
  have hd := norm_pos D hD
  have he := norm_pos E hE
  have hr := active_norm_pos C D
  have hz : 0< Z := zero_lt_one.trans hZ
  cases reflected <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals
    unfold frequencyRadius mainCommonRadius nominalLog
    rw [nominal_equal_support C D E hC hD heq K V]
    simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    norm_num only [Nat.cast_ofNat]
    by_cases h : Real.logb Z (C.absNorm:ℝ)≤ Real.logb Z (D.absNorm:ℝ)
    · rw [max_eq_right (show Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ)≤0 by linarith),
        max_eq_left (show 0≤ Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ) by linarith)]
      ring
    · rw [max_eq_left (show 0≤ Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ) by linarith),
        max_eq_right (show Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)≤0 by linarith)]
      ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_child_source_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_fourier_scale_upper

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_fourier_frequency_log

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondChildCaps -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySecondCaps; sha256 4b225dedd07e333c6f750accbcb54916ae6c49f7ee3e5a91fac7b38b37cd278e -/
section
                                                   
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- The actual label-dependent cutoff satisfies the polynomial envelope
needed for second-dyad selection. It holds for either first rectangle. -/
theorem actual_geometry_main_cutoff_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ sigma reserve b M : ℝ)
    (N : ℕ)(hK : 0< K)(hZ : 1< Z)(hb : 0< b)(hξ : 0≤ξ)
    (hsigma : 0≤ sigma)(hreserve : 0≤ reserve)(hKM : K≤ Z^M)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
      (geometryFirstLabel s R seed K Z ξ hK key j)) Z ξ≤ b^(2*N)*Z^(M+ξ/2) := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  have hh := main_fourier_scale_upper reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported src.C src.D src.hC src.inactive).1
    src.sameSupport K (volume s) Z sigma (frequencyLoss Z 32 ξ) reserve b N
    hK (volume_pos s) hZ hb hsigma (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hreserve
  change firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
    (geometryFirstLabel s R seed K Z ξ hK key j)≤ b^(2*N)*K at hh
  unfold frequencyRadius
  calc
    _≤(b^(2*N)*K)*Z^(ξ/2) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by linarith) _)
    _≤(b^(2*N)*Z^M)*Z^(ξ/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKM (pow_nonneg hb.le _)) (Real.rpow_nonneg (by linarith) _)
    _=_ := by rw [Real.rpow_add (zero_lt_one.trans hZ)];ring

/-- A single threshold bounds all supported first-child source radii.
It is fixed before the original source, the selected columns and allocations. -/
theorem eventual_geometry_child_source_cap (N : ℕ)(b bs ε : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι][DecidableEq ι]
      (s : Input ι)(A : ℝ),Fintype.card ι≤ N → Endpoints b bs bs s → volume s≤ Z^A →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ),
      frozenCoefficient B.val C R s.ν s.W s.P≠0 → sourceRadius (child s C R B χ t)≤ Z^(A+ε) := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually
    (eventually_ge_atTop (geometry N b bs bs)),eventually_gt_atTop (1:ℝ)] with Z hgeom hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ s A hcard he hV C R B χ t hne
  have hn := norm_ge_one C (allocation_ne s C B)
  have hg : 0≤ geometry N b bs bs := (geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)
  calc
    _≤ geometry N b bs bs*volume s/(C.absNorm:ℝ) :=
      actual_common_child_source_cap N b bs hb hbs s hcard he C R B χ t hne
    _≤ geometry N b bs bs*volume s := div_le_self (mul_nonneg hg (volume_pos s).le) hn
    _≤ Z^ε*Z^A := mul_le_mul hgeom hV (volume_pos s).le (Real.rpow_nonneg (by linarith) _)
    _=_ := by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_cutoff_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_geometry_child_source_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySecondCaps -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryTail; sha256 fb87873dc7fdf8d9ba6e64e92e5ee82fe3f81763130d2255a735600cf55257c1 -/
section
                                                                 

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
local instance geometryTailDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- One tail constant and threshold work before the surviving slot subset
is chosen. The bound is for the literal original discarded energy. -/
theorem actual_subset_second_tail {α : Type*}[Fintype α][DecidableEq α]
    (b wlo whi B ξ saving : ℝ)(hb : 0≤ b)(hwlo : 0< wlo)
    (hwhi : 0≤ whi)(hB : 0≤ B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(J : Finset α)(s : Input J)(W₁ W₂ : 𝓢(ℝ,ℂ)),s.W₁=W₁ → s.W₂=W₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi →
      (∀i,s.hi i≤ b) → ∀(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),
      0< K → volume s.toData≤ Z^B → Tsec≤ Z^B → (volume s.toData)^2/K≤ Tsec →
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  have hex (J : Finset α) := second_input_tail_arbitrary_saving (fun _ : J=>b)
    wlo whi B ξ saving (fun _=>hb) hwlo hwhi hB hξ
  choose F C hC hbound using hex
  let F₀ := Finset.univ.biUnion F
  let C₀ := ∑J : Finset α,C J
  have hCp : 0< C₀ := Finset.sum_pos (fun J _=>hC J) Finset.univ_nonempty
  refine ⟨F₀,C₀,hCp,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro J s W₁ W₂ he₁ he₂ hs₁ hs₂ hhi R seed Φ K Tsec hK hV hT hnom
  have ht := (hZ J).2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hhi R seed Φ K Tsec hK hV hT hnom
  have hCJ : C J≤ C₀ := Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
  have hF : (F J).sup (schwartzSeminormFamily ℝ ℝ ℂ)≤ F₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.sup_mono (Finset.subset_biUnion_of_mem F (Finset.mem_univ J))
  have hFΦ := hF Φ
  have hzpos : 0< Z := zero_lt_one.trans (hZ J).1
  have hCJpos := (hC J).le
  have hfinal : C J*(plainControl s W₁ W₂)^2*(F J).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving)≤
      C₀*(plainControl s W₁ W₂)^2*F₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
    gcongr
  exact le_trans ht hfinal

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_subset_second_tail

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryTail -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalCapacity.Geometry; sha256 d2655b378cc8987bd37e00d635c7d4ab380262c8974db3dfd288e864004e5f8f -/
section
                                                            
                                                                       

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondActualWidth CenteredMomentCanonicalFirst
open CenteredMomentSourceRow CenteredMomentSupport CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

/-- The actual common frequency ideal divides each genuine common allocation. -/
theorem actual_common_norm_le (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) :
    normValue (commonFrequencyGenerator C D) ≤ (C.absNorm:ℝ) := by
  have hd := (commonFrequencyGenerator_dvd C D hC hD hCD).1
  have hi : Ideal.span {commonFrequencyGenerator C D} ∣ C := by
    have hh := Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)
    simpa only [primary_span_supported C hC] using hh
  unfold normValue
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm hi)

/-- The same actual common frequency ideal divides the right allocation. -/
theorem actual_common_norm_le_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) :
    normValue (commonFrequencyGenerator C D) ≤ (D.absNorm:ℝ) := by
  have hd := (commonFrequencyGenerator_dvd C D hC hD hCD).2
  have hi : Ideal.span {commonFrequencyGenerator C D} ∣ D := by
    have hh := Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)
    simpa only [primary_span_supported D hD] using hh
  unfold normValue
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)) (map_dvd Ideal.absNorm hi)

/-- The unit subset has positive ideal norm; its logarithm cannot enlarge
 the common frequency shift. -/
theorem actual_unit_log_nonneg (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ Real.logb Z ((∏ P ∈ U,P.val).absNorm:ℝ) := by
  have hn : (∏ P ∈ U,P.val) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun P _ => (commonPrime_supported_ideal C D hC P).1)
  exact Real.logb_nonneg hZ (norm_ge_one _ hn)

/-- This is the literal second-transform shift, with the actual common
 frequency generator and actual partition unit ideal. -/
theorem actual_common_shift_le (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (normValue (commonFrequencyGenerator C D))-
      Real.logb Z ((∏ P ∈ U,P.val).absNorm:ℝ) ≤ Real.logb Z (C.absNorm:ℝ) := by
  have hg := Real.logb_le_logb_of_le hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C D hC))
    (actual_common_norm_le C D hC hD hCD)
  linarith [actual_unit_log_nonneg C D hC U Z hZ]

/-- Right-source cancellation uses the very same generator and partition U. -/
theorem actual_common_shift_le_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (normValue (commonFrequencyGenerator C D))-
      Real.logb Z ((∏ P ∈ U,P.val).absNorm:ℝ) ≤ Real.logb Z (D.absNorm:ℝ) := by
  have hg := Real.logb_le_logb_of_le hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C D hC))
    (actual_common_norm_le_right C D hC hD hCD)
  linarith [actual_unit_log_nonneg C D hC U Z hZ]

#print axioms actual_common_norm_le_right
#print axioms actual_common_shift_le_right
#print axioms actual_common_norm_le
#print axioms actual_unit_log_nonneg
#print axioms actual_common_shift_le
end
end OAI.SevenEighths.Cycle61FinalCapacity

end
/- END ORIGINAL Cycle61.Physical.FinalCapacity.Geometry -/
