/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B004
import Submissions.local44_20261013.Bundles.B005
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B026
import Submissions.local44_20261013.Bundles.B027
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowDirect
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflectionError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

/- BEGIN ORIGINAL MODULE Analytic.LocalAmplifier ; sha256 9fc243247ec199d36d6d458ae970279f3f514921aad630f3e6fdb5470e8c07ea -/
section



/-! The actual annular amplifier has a stronger lower prime length than
the coarse bound in the incumbent wrapper. This sharper lower length is
needed by the three extracted-error reserves. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationEnergy
open CenteredMomentGaussNormalization CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem local_parent_geometry (n₁ n₂ z : ℝ)
    (hn₁ : n₁ ≤ 423/1000) (hn₂ : n₂ ≤ 423/1000) (hz : z ≤ 37/1000)
    (hcap : n₁+n₂+(22/5)*z ≤ 1) :
    n₁+n₂+z ≤ 881/1000 ∧
      0 ≤ max (n₁+n₂+(9/2)*z-1) 0 ∧
      max (n₁+n₂+(9/2)*z-1) 0 ≤ 37/10000 := by
  refine ⟨by linarith, le_max_right _ _, ?_⟩
  exact max_le (by linarith) (by norm_num)

theorem eventually_pool_prime_quarter_lower (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes ⊆ Sbad) (sigma : ℝ) (hsigma : 0 < sigma) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ p : O,
      p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))) →
      sigma/4 ≤ Real.logb Z (normValue p) ∧ Real.logb Z (normValue p) ≤ sigma/3 := by
  have hg := (tendsto_rpow_atTop (show 0 < sigma/12 by linarith)).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hg,eventually_gt_atTop (1 : ℝ)] with Z hgap hZ
  refine ⟨hZ,?_⟩
  intro p hp
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p hp
  have hb := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3))
    (Finset.mem_sdiff.mp hd.2.1).1
  have hhalf : Z^(sigma/3)/2 ≤ normValue p := by
    change Z^(sigma/3)/2 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)
    linarith [hb.1]
  have hsplit : Z^(sigma/3) = Z^(sigma/4)*Z^(sigma/12) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  have hpow : Z^(sigma/4) ≤ normValue p := by
    have hm := mul_le_mul_of_nonneg_left hgap
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le (sigma/4))
    rw [hsplit] at hhalf
    nlinarith
  have hlog := Real.logb_le_logb_of_le hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/4)) hpow
  rw [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hlog
  exact ⟨hlog,(pool_prime_log_range M H Sbad hbad Z sigma hZ p hp).2⟩

theorem actual_amplification_error_reserve (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes ⊆ Sbad) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ p : O,
      p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))) →
      ∀ g : ℝ, g ≤ 37/10000 → ∀ k : ℕ, (k=1 ∨ k=6 ∨ k=7) →
      53/60000 ≤ errorRemoval p Z k-
        (g+9/500+errorRemoval p Z k-errorMoving p Z k)/6 := by
  filter_upwards [eventually_pool_prime_quarter_lower M H Sbad hbad (9/500) (by norm_num)]
    with Z hZ
  refine ⟨hZ.1,?_⟩
  intro p hp g hg k hk
  have hl := (hZ.2 p hp).1
  have hr := local_amplification_error_reserves g (Real.logb Z (normValue p)) hg (by linarith)
  rcases hk with rfl | rfl | rfl
  · simpa only [errorRemoval,errorMoving,Nat.cast_one,one_mul,ite_false,
      show ¬(1 : ℕ)=6 by decide] using hr.1
  · norm_num only [errorRemoval,errorMoving] at ⊢
    simpa using hr.2.1
  · norm_num only [errorRemoval,errorMoving] at ⊢
    exact hr.2.2

/-- The chosen enlarged smooth ball majorizes the literal amplified row;
its larger radius is passed to Poisson as an actual kernel parameter. -/
theorem actual_enlarged_amplified_ball (Z K₀ c d a ω : ℝ) (hZ : 1 ≤ Z)
    (hω : 0 ≤ ω) (h p : O) (hh : normValue h ≤ Z^K₀) (hp : normValue p ≤ Z^a) :
    1 ≤ (ballProfile (‖eisEmbedding (p^6*h)‖^2 /
      Z^(K₀+max (d-c) 0+6*a+ω))).re := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos hZpos _) _
  have hb := outputRow_norm (h,p) Z K₀ a hZpos hh hp
  change normValue (p^6*h) ≤ Z^(K₀+6*a) at hb
  exact hb.trans (Real.rpow_le_rpow_of_exponent_le hZ
    (by linarith [le_max_right (d-c) (0 : ℝ)]))

#print axioms actual_amplification_error_reserve
#print axioms actual_enlarged_amplified_ball
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.LocalAmplifier -/

/- BEGIN ORIGINAL MODULE Analytic.NaturalZeroTransport ; sha256 fe903a5eaf5ea721c14ca497a8dc72b69fee818263d63c03ae7e939ad6233a0b -/
section



/-! The retained cancellation holes preserve the actual positive-real zero
set and every buffered detector maximum, including the baseline and bin
boundaries. Nonprincipality follows from the literal fixed-inducing gate. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeFiniteDeletion HeckeDetectorZeros
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredExceptionalProfile LocalMoment ConcretePrimeRowBridge

local notation "O" => HeckeFamily.O

theorem excluded_modulus_mask (χ : Character) (R I : Ideal O) :
    idealCoeff (excluded χ R) I =
      if IsCoprime I (excluded χ R).modulus then idealCoeff χ I else 0 :=
  excludePrimes_mask χ (CompletedGauss.primeSupport R) (support_prime R) I

theorem excluded_nonprincipal (χ : Character) (R : Ideal O) (hχ : χ.residue ≠ 1) :
    (excluded χ R).residue ≠ 1 :=
  fun h => hχ ((principal_iff_of_mask (excluded χ R) χ
    (excluded_modulus_mask χ R)).mp h)

theorem excluded_positive_zeros (χ : Character) (R : Ideal O) (hχ : χ.residue ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction (excluded χ R) s = 0 ↔ LFunction χ s = 0 :=
  positive_zeros_eq_of_mask (excluded χ R) χ (excluded_nonprincipal χ R hχ)
    (excluded_modulus_mask χ R) hs

theorem excluded_zeroMaximum {Label : Type*} [Fintype Label]
    (χ : Label → Character) (R : Label → Ideal O)
    (hχ : ∀ label, (χ label).residue ≠ 1) (T : ℝ) :
    zeroMaximum (fun label => excluded (χ label) (R label))
      (fun label => excluded_nonprincipal (χ label) (R label) (hχ label)) T =
      zeroMaximum χ hχ T := by
  apply zeroMaximum_eq_of_mask
  intro label I
  exact excluded_modulus_mask (χ label) (R label) I

/-- For a genuine natural row the original fixed-inducing exclusion is
sufficient. No primitive-character substitution or zero-density assumption
is used to pass through the finite puncture. -/
theorem naturalRow_excluded_positive_zeros {η : Character} {w : O}
    (N : NaturalRow η w) (hw : w ≠ 0) (Q R : Ideal O) (hR : R ≠ 0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask * idealGenerator R) 1 w)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction (excluded N.character R) s = 0 ↔ LFunction N.character s = 0 :=
  excluded_positive_zeros N.character R (N.nonprincipal hw Q R hR hex) hs

#print axioms naturalRow_excluded_positive_zeros
#print axioms excluded_zeroMaximum

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.NaturalZeroTransport -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainMarkedState ; sha256 b16175cfc16bdf30acc9abe2ff09db6709de71516f2dddb8c12a625202c42958 -/
section






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainMarkedState Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary Cycle25CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource Cycle25CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open Cycle25CenteredMomentDetectorPlainSlotProfile Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainSlotProfile CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {D:Cycle25.Weighted.MomentData}

theorem weighted_source_slot_coefficient (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(η:Character)(s:Slot)
    (hreal:(F.external s).re=17/50)(hU:0< U)(I:Ideal O):
    idealCoeff η.inverse I*slotWindow F s ((I.absNorm:ℝ)/(U^(F.widths s)))=
      idealCoeff η.inverse I*annularWeight (fun x=> conj (S.W x))
        (U^(F.widths s)) (33/50) (-(F.external s).im) I := by
  have he:=weighted_physical_annular_all S η (U^(F.widths s)) (Real.rpow_pos_of_pos hU _)
    (F.external s) I
  rw [hreal] at he
  norm_num at he
  simpa only [physicalSlotCoefficient,slotWindow,hprofile] using he

theorem weighted_retained_eq_initial_energy (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(hupper:∀s,F.upper s=2)
    (η:Character)(Q:Ideal O)(selected:Finset Slot)
    (hreal:∀s∈selected,(F.external s).re=17/50)
    (Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)(hU:1 ≤ U)(hδ:0 ≤ δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0 ≤ (Φ x).re)
    (hη:(η.modulus.absNorm:ℝ) ≤ U^δ)(j k:ℕ)(σ t:ℝ):
    let state:=weighted_initialState η Q Φ bΦ U δ hU hδ hs hp hη
    weighted_retainedSourceEnergy state.radial.keep F η selected j k σ t Φ=
      energy state.character state.mask 1 0
        ((weighted_detectorProfiles F.reverse j k σ t).profile 0)
        ((weighted_detectorProfiles F.reverse j k σ t).profile 1)
        (fun s:selected=> CenteredMomentPrimeSlot.primePool M H 2 (U^(F.widths s.val)))
        (fun (s:selected) I=> idealCoeff η.inverse I*
          annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
            (-(F.external s.val).im) I)
        (fun s:selected=> U^(F.widths s.val)) (U^F.m) (U^F.m)
        state.radial.keep state.radial.profile state.radial.scale := by
  dsimp only
  change retainedSourceEnergy _ F η selected j k σ t Φ = _
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  have hc:(fun (s:selected) I=> idealCoeff η.inverse I*
      slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))=
      (fun (s:selected) I=> idealCoeff η.inverse I*
        annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I):=by
    funext s I
    exact weighted_source_slot_coefficient S F hprofile η s.val (hreal s.val s.property)
      (zero_lt_one.trans_le hU) I
  rw [hc]
  simp only [hupper,plainProfile_eq_detectorSchwartz,weighted_initialState,NaturalState.mask,
    weighted_detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
  norm_num

theorem weighted_plain_length_eq [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U):
    length U (U^F.m)=F.m := by
  have hm:0 ≤ F.m:=(F.lengths hU).2.2.2.2
  rw [length,max_eq_right (Real.one_le_rpow hU.le hm),
    Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem weighted_marked_capacity [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U)
    (selected:Finset Slot)(κ δ:ℝ)(hδ:0 ≤ δ)
    (hcap:2*F.m+6*κ*(∑s∈selected,F.widths s) ≤ 1):
    length U (U^F.m)+length U (U^F.m)+6*κ*(∑s:selected,F.widths s.val) ≤ 1+δ := by
  rw [weighted_plain_length_eq F hU,Finset.sum_coe_sort]
  linarith

theorem weighted_source_batch_marked_initial (κplain:ℝ) (S:Cycle25ProbeFinalAssembly.WeightedSourceData D):
    ∃bΦ:ℝ,0< bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ) ≤ d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*κplain*(∑s∈selected,F.widths s) ≤ 1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (weighted_sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=weighted_initialKeep η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*κplain*(∑s:selected,F.widths s.val) ≤ state.width ∧
        (∀s:selected,0< F.widths s.val ∧ F.widths s.val ≤ F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2) ≤ 
          energy state.character state.mask 1 0
            ((weighted_detectorProfiles F.reverse j k σ t).profile 0)
            ((weighted_detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=> CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=> idealCoeff η₀.inverse I*
              annularWeight (fun x=> conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=weighted_radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [weighted_source_label_modulus_eventually S η δ hδ,weighted_source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0< d:=by linarith
  have hU:1< Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ) ≤ (Z^d)^δ:=hz.2 label d hd
  let state:=weighted_initialState η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact weighted_marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=weighted_retained_eq_initial_energy S F hprof hupper η₀ (internalQ (weighted_sourceFixedIdeal S) η₀) selected
      (fun s _=> hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end SevenEighths.Cycle25CenteredMomentDetectorPlainMarkedState

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorPlainMarkedState -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentInput ; sha256 40bc477e73c2151476ead10b86258d3264efd09e8bfb4a36f5cdef94de923559 -/
section





namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters Cycle25ProbeHighRowFamily
open HeckeInverseAmplification

def weighted_SourceMomentBound {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (κplain : ℝ) (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100< a → a ≤ 7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im| ≤ height →
    Cycle25ProbeHighRowFamily.SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z κplain counts.c counts.k C height D.t

lemma weighted_SourceMomentBound.mono_constant {D : Cycle25.Weighted.MomentData}
    {F : WeightedSourceData D} {κplain : ℝ}
    {counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤ Z) (h : weighted_SourceMomentBound F κplain counts η Z τ C height)
    (hC : C≤ C') : weighted_SourceMomentBound F κplain counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots hwidth
    hprof hupp hext hmesh hbin hfam bin j J K hne
  have hm := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  refine ⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩
  intro selected hsel hcap j k hj s hs t ht
  exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentInput -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.OriginalMomentInput ; sha256 f3cdd53f3ac2a724354143e667ebd2588ac08f58b320318d4c6f974990fce81c -/
section





namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters Cycle25ProbeHighRowFamily
open HeckeInverseAmplification

def old_sourceMomentBound {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (counts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100< a → a ≤ 7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im| ≤ height →
    ProbeHighRowFamily.SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z 0 counts.cB counts.kB C height D.t


lemma old_sourceMomentBound.mono_constant {D : Cycle25.Weighted.MomentData}
    {F : WeightedSourceData D} {counts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤ Z) (h : old_sourceMomentBound F counts η Z τ C height) (hC : C≤ C') :
    old_sourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact ProbeFinalAssembly.sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S
    F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ
    (7/8) 2 D.t D.t i z 0 counts.cB counts.kB C C' height D.t hZ hC
    (h rows d a hd hd' ha ha' hrows i z hz hzh)

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.OriginalMomentInput -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionDeleted ; sha256 eebdf75ee01ee68b09da88902b08091ceec94aa37c13d1ef62b190dcd3bb5ef2 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/OriginalHighReflectionDeleted.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionDeleted
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyOriginalHighReflectionGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem deleted_original_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi≤ s.width/16 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=> heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=Real.logb Z (X₁/((∏I∈D₁,I).absNorm:ℝ))
  let along:=Real.logb Z (X₂/((∏I∈D₂,I).absNorm:ℝ))
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=> hw i)
  have hg:=actual_deleted_gates s hZ.1 (by linarith) hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=> hw i)) hsum hsumle hκ hxi.le hxiM hshort hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤ L:=by linarith [s.width_nonneg]
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=> Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=> polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=> polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.Cycle25CenteredMomentEnergyOriginalHighReflectionDeleted

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.OriginalHighReflectionDeleted -/
