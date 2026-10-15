/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B107
import Submissions.cycle61_c0125139.Bundles.B109
import Submissions.cycle61_c0125139.Bundles.B123
import Submissions.cycle61_c0125139.Bundles.B124
import Submissions.cycle61_c0125139.Bundles.B128
import Submissions.cycle61_c0125139.Bundles.B129

/- BEGIN ORIGINAL Cycle61.Moment.ProfileShellEnergy; sha256 f49d8a9d452f61bef7e12c09a7a006ebfa32af9a53cfbefacf073555f5b107e2 -/
section
                                      
                                       
                                         

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle61HighResidual Cycle61HighProfiles CenteredMomentFiniteProfileExceptional
open Cycle61FinalLow CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance profileShellFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The original row and character are retained while the two smooth plain
functions are normalized at their actual post-allocation scales. -/
def profileWholeDatum {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (s : Data ι) (second : Bool)
    (L : Ideal O) (alloc : Allocation L (Finset.univ : Finset (ι⊕Fin 2)))
    (w σ v : ι→ℝ) (θ : ι→ RayQuotient.Characters M H)
    {ap bp : ℝ} (hap : 0< ap) (S : Finset (ℕ×ℕ)) (p : Profiles ap bp) :=
  wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
    (normalizedData hap S p (profileScales s second L alloc)
      (profile_scales_pos s second L alloc) s) second L alloc w σ v θ (ap/max 1 bp) bp

/-- Uniform high-row estimates are applied to normalized profiles; the
original profile control is restored before contracting residual allocations.
Rows killed by their plain support require no analytic admissibility gate. -/
theorem actual_profile_high_retained_family {Index : Type} [Fintype Index]
    (Slots : Index→ Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤ N)
    (P : HighSourceParameters) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap) :
    ∃ n : ℕ, ∃ C : ℝ, 0< C ∧ ∀η₀ : Character,
      ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      ∀a : ℝ,51/100≤ a → a≤1 → ∀i : ℕ,
      ∀l : Index, ∀s : Data (Slots l),
      ∀st : NaturalState Z P.Bmask P.bΦ,
      ∀(hQM : st.fixedModulus≤ M)(hQη : st.fixedModulus≤η₀.modulus)
        (z : O)(hz : st.radial.keep z),
      ∀(w σ v : Slots l→ℝ)(θ : Slots l→ RayQuotient.Characters M H),
      ∀(F G : Finset (ℕ×ℕ)), (0,0)∈F → ∀p : Profiles ap bp,
      s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) → s.b₁=bp → s.b₂=bp →
      ∀Ds : Finset (Ideal O), (∀L∈Ds,Squarefree L) →
      ∀T e Cprofile : ℝ,1≤ T → 0≤ Cprofile →
      (∀L∈Ds,T≤(L.absNorm:ℝ)) → (∀L∈Ds,(L.absNorm:ℝ)<2*T) →
      (∀L∈Ds,∀alloc∈s.toSource.active L,∀b : Bool,
        Cycle61.Physical.sourcePositiveRow s.toSource b L alloc z≠0 →
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z st hQM hQη z hz s b L alloc w σ v θ hap F p)) →
      (∀L∈Ds,∀alloc∈s.toSource.active L,∀b : Bool,
        clippedControl hap F p (profileScales s b L alloc) (profile_scales_pos s b L alloc) 0*
          clippedControl hap F p (profileScales s b L alloc) (profile_scales_pos s b L alloc) 1≤
          Cprofile*p.control G) →
      (∀L∈Ds,∀alloc∈s.toSource.active L,∀b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
          s b L alloc w σ v θ ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*N-
          Cycle61.Physical.sourcePostClip s.toSource b Z L alloc≤ e) →
      (∑L∈Ds,∑alloc∈s.toSource.active L,retainedAllocationCost s L alloc z) ≤
        C*Cprofile^2*(p.control G)^2*(wholeControl s)^2*(2*T)^(2*ε)*
          Z^(e+s.toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂]) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hactual⟩ := actual_high_source_datum M H hH P
  have he (l : Index) := retained_pair_shell N (hN l) (hN l) ε hε
  choose Cshell hCshell hsh using he
  let Csh := 1+∑l,Cshell l
  have hCsh : 0< Csh := by
    dsimp [Csh]
    have := Finset.sum_nonneg (fun l (_ : l∈Finset.univ)=>(hCshell l).le)
    linarith
  have hshell (l : Index) : RetainedPairShellBound (Slots l) (Slots l) Csh ε := by
    apply (hsh l).mono
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.univ)=>(hCshell k).le)
      (Finset.mem_univ l)
    dsimp [Csh]
    linarith
  let K := Cp^2*(max 1 Cs)^(N)
  have hK : 0< K := mul_pos (sq_pos_of_pos hCp)
    (pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _)
  refine ⟨n,4*K*Csh,by positivity,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i l s st hQM hQη z hz w σ v θ F G hF p hW₁ hW₂ hb₁ hb₂
    Ds hDs T e Cprofile hT hCprofile hlo hhi hvalid hcontrol hexp
  have hZp : 0< Z := zero_lt_one.trans hZ.1
  let Kp := Cprofile^2*(p.control G)^2*K
  have hKp : 0≤ Kp := by dsimp [Kp]; positivity
  have hpoint (L : Ideal O) (hL : L∈Ds)
      (alloc : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2)))
      (halloc : alloc∈s.toSource.active L) (b : Bool) :
      (normalizedPositiveNorm s.toSource b Z L alloc z)^2≤ Kp*Z^e := by
    by_cases hn : Cycle61.Physical.sourcePositiveRow s.toSource b L alloc z=0
    · simp only [normalizedPositiveNorm,hn,norm_zero,zero_div,zero_pow (by norm_num : 2≠0)]
      positivity
    let D := profileWholeDatum M H hH P η₀ Z st hQM hQη z hz s b L alloc w σ v θ hap F p
    have hcard : D.liveCard P≤ N := by
      change (liveIndices L alloc).card≤ N
      exact (Finset.card_le_univ _).trans (hN l)
    have hc := high_source_datum_cap M H P hZ.1.le hCs.le (by linarith : 1/2≤ a)
      (hZ.2 a ha ha' i D (hvalid L hL alloc halloc b hn)) le_rfl hcard
    have hret : ∀j,1≤ profileScales s b L alloc j*bp := by
      have hh := profile_scales_survive s b L alloc z hn
      rw [hb₁,hb₂] at hh
      intro j; fin_cases j
      · exact hh.1
      · exact hh.2
    have hr := sourcePositiveRow_normalized_bound hap F hF p _ (profile_scales_pos s b L alloc)
      hret s hW₁ hW₂ b L alloc z G Cprofile
      (K*Z^((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(N)))
      hCprofile (hcontrol L hL alloc halloc b) hc
    have hp := normalizedPositiveNorm_sq_bound s.toSource b Z hZp L alloc z Kp
      ((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(N))
      (hr.trans_eq (by dsimp [Kp]; ring))
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ hKp
    apply Real.rpow_le_rpow_of_exponent_le hZ.1.le
    exact hexp L hL alloc halloc b
  have hpairs (L : Ideal O) (hL : L∈Ds)
      (x : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2))) (hx : x∈s.toSource.active L)
      (y : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2))) (hy : y∈s.toSource.active L)
      (b c : Bool) : normalizedPositiveNorm s.toSource b Z L x z*
        normalizedPositiveNorm s.toSource c Z L y z≤ Kp*Z^e := by
    have hhx := hpoint L hL x hx b
    have hhy := hpoint L hL y hy c
    nlinarith [sq_nonneg (normalizedPositiveNorm s.toSource b Z L x z-
      normalizedPositiveNorm s.toSource c Z L y z)]
  have hbound := hshell l s s Ds hDs (fun _ _ _=>z) (fun _ _ _=>z) T Z
    hT hZ.1 hlo hhi (fun _ _=>Kp*Z^e) (fun _ _=>by positivity) hpairs
  calc
    _ ≤ ∑L∈Ds,∑x∈s.toSource.active L,∑y∈s.toSource.active L,
        Real.sqrt (retainedAllocationCost s L x z)*Real.sqrt (retainedAllocationCost s L y z) :=
      Finset.sum_le_sum (fun L _=>diagonal_retained_cost_le_pairs s L z)
    _ ≤ _ := hbound.trans_eq (by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,Nat.cast_ofNat,nsmul_eq_mul]
      rw [show e+s.toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂] =
        e+(s.toSource.allowance Z+s.toSource.allowance Z+
          Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂]+
          Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂])/2 by ring,
        Real.rpow_add hZp]
      dsimp [Kp]
      ring)

/-- Uniform high-row estimates are applied to normalized profiles; the
original profile control is restored before contracting residual allocations.
Rows killed by their plain support require no analytic admissibility gate. -/
theorem actual_profile_high_retained_shell {α : Type} [Fintype α] [DecidableEq α]
    (P : HighSourceParameters) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap) :
    ∃ n : ℕ, ∃ C : ℝ, 0< C ∧ ∀η₀ : Character,
      ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      ∀a : ℝ,51/100≤ a → a≤1 → ∀i : ℕ,
      ∀S : Finset α, ∀s : Data S,
      ∀st : NaturalState Z P.Bmask P.bΦ,
      ∀(hQM : st.fixedModulus≤ M)(hQη : st.fixedModulus≤η₀.modulus)
        (z : O)(hz : st.radial.keep z),
      ∀(w σ v : S→ℝ)(θ : S→ RayQuotient.Characters M H),
      ∀(F G : Finset (ℕ×ℕ)), (0,0)∈F → ∀p : Profiles ap bp,
      s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) → s.b₁=bp → s.b₂=bp →
      ∀Ds : Finset (Ideal O), (∀L∈Ds,Squarefree L) →
      ∀T e Cprofile : ℝ,1≤ T → 0≤ Cprofile →
      (∀L∈Ds,T≤(L.absNorm:ℝ)) → (∀L∈Ds,(L.absNorm:ℝ)<2*T) →
      (∀L∈Ds,∀alloc∈s.toSource.active L,∀b : Bool,
        Cycle61.Physical.sourcePositiveRow s.toSource b L alloc z≠0 →
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z st hQM hQη z hz s b L alloc w σ v θ hap F p)) →
      (∀L∈Ds,∀alloc∈s.toSource.active L,∀b : Bool,
        clippedControl hap F p (profileScales s b L alloc) (profile_scales_pos s b L alloc) 0*
          clippedControl hap F p (profileScales s b L alloc) (profile_scales_pos s b L alloc) 1≤
          Cprofile*p.control G) →
      (∀L∈Ds,∀alloc∈s.toSource.active L,∀b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
          s b L alloc w σ v θ ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
          Cycle61.Physical.sourcePostClip s.toSource b Z L alloc≤ e) →
      (∑L∈Ds,∑alloc∈s.toSource.active L,retainedAllocationCost s L alloc z) ≤
        C*Cprofile^2*(p.control G)^2*(wholeControl s)^2*(2*T)^(2*ε)*
          Z^(e+s.toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂]) := by
  exact actual_profile_high_retained_family M H hH (fun S : Finset α=>↥S)
    (Fintype.card α) (fun S=>by simpa using Finset.card_le_univ S) P ε hε hap

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.actual_profile_high_retained_shell

#print axioms OAI.SevenEighths.Cycle61Moment.actual_profile_high_retained_family

end
/- END ORIGINAL Cycle61.Moment.ProfileShellEnergy -/

/- BEGIN ORIGINAL Cycle61.Moment.ProfileCommonAdmissible; sha256 48fa28e7f7ea7a9dc1c3211576ca8f020ef153c2391c9e853032afdd5065f2b6 -/
section
                                        
                                           
                                    
                                          

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open CenteredMomentFiniteProfileExceptional Cycle61HighProfiles Cycle61FinalLow
open ConcreteTraceCRT HeckeDetectorZeros
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance profileCommonFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Each literal common allocation and residual plain divisor can only
reduce a positive plain scale. -/
theorem common_profile_scale_le {α : Type} [Fintype α] [DecidableEq α]
    (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (j : Fin 2) :
    profileScales (commonData (withHeight s τ t) C R B) second L alloc j ≤
      Cycle61.Physical.sourcePlainScales s.toData.toSource second j := by
  let src := commonData (withHeight s τ t) C R B
  have hlast : (1:ℝ)≤(selectedPlain L alloc j).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ alloc (Sum.inr j)))
  have hfirst : (1:ℝ)≤(B.val (Sum.inr j)).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (alloc_ne s C B (Sum.inr j)))
  apply (div_le_self (LowBranch.source_plain_positive src second j).le hlast).trans
  cases second <;> fin_cases j
  · exact div_le_self s.X₁_pos.le hfirst
  · exact div_le_self s.X₂_pos.le hfirst
  · exact div_le_self s.Y₁_pos.le hfirst
  · exact div_le_self s.Y₂_pos.le hfirst

/-- The original plain cap therefore supplies the normalized high-source
scale gate, including clipping at one. -/
theorem actual_common_clipped_scale_cap {α : Type} [Fintype α] [DecidableEq α]
    (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t Z cap d Rp : ℝ) (hZ : 1≤ Z) (hdRp : 0≤ d*Rp)
    (hcap : cap≤ d*Rp)
    (horiginal : ∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (j : Fin 2) :
    clippedScale (profileScales (commonData (withHeight s τ t) C R B) second L alloc j)≤ Z^(d*Rp) := by
  apply max_le (Real.one_le_rpow hZ hdRp)
  exact (common_profile_scale_le s C R B τ t second L alloc j).trans
    ((horiginal second j).trans (Real.rpow_le_rpow_of_exponent_le hZ hcap))

/-- Admissibility of the actual common-allocated source. Slot coefficients
come from the original ray dictionary, and plain bounds come from the
uniform clipped normalization. Only geometric and height gates remain. -/
theorem actual_common_profile_admissible {α : Type} [Fintype α] [DecidableEq α]
    (P : HighSourceParameters) (η₀ : Character) (Z a t : ℝ) (hZ : 1< Z) (ha : a≤1)
    (i n : ℕ) (s : Input α) (θ : α→ RayQuotient.Characters M H) (w σ v : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z)
    (C R : Ideal O) (B : actualAllocations s.pools C)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (hmask : st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*
      ConcretePrimeRowBridge.idealGenerator (R*C))
    (z : O) (hz : st.radial.keep z)
    (hwidth : st.width≤ P.Mcap)
    (hradial : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0)
    (hupper : zeroMaximum
      (wholeSourceFamily M H hH η₀
        (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture))
      (whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _)
        (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e)
    (hmod : ((excluded (naturalRow st.character z (st.row_ne_zero z hz)).character
      st.puncture).modulus.absNorm:ℝ)≤ Z^P.d)
    (hw : ∀j,0≤ w j) (hwr : ∀j,w j/P.d≤ P.Rwidth)
    (hσlo : ∀j,P.σmin≤σ j) (hσhi : ∀j,σ j≤ P.σmax)
    (hfreq : ∀j,|t+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)
    (hslotheight : (3+(3*i+2:ℕ)*Z^P.τ)^2≤(Z^P.d)^P.vslot)
    (hplainfreq : |t|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)
    (hplainheight : (3+(3*i+2:ℕ)*Z^P.τ)^4≤(Z^P.d)^P.vplain)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    {ap bp : ℝ} (hap : 0< ap) (F : Finset (ℕ×ℕ)) (p : Profiles ap bp)
    (hW₁ : s.W₁=(p.profile 0:ℝ→ℂ)) (hW₂ : s.W₂=(p.profile 1:ℝ→ℂ)) :
    let src := commonData (withHeight s st.character t) C R B
    let U := profileScales src second L alloc
    let hU := profile_scales_pos src second L alloc
    (∀j,clippedScale (U j)≤ Z^(P.d*P.Rplain)) →
    (∀j,Function.support (dilated ((normalizedPlains hap F p U hU).profile j)
      (clipDilation (U j)))⊆Icc (ap/max 1 bp) bp) →
    (∀j,ContDiff ℝ ∞ (dilated ((normalizedPlains hap F p U hU).profile j)
      (clipDilation (U j)))) →
    (∀j k,(k=2 ∨ k=n+2) → ∀x∈Icc (-1:ℝ) 2,∀u : ℝ,
      (1+|u|)^k*‖mellin (dilated ((normalizedPlains hap F p U hU).profile j)
        (clipDilation (U j))) ((x:ℂ)+u*Complex.I)‖≤ P.profileBound k) →
    HighSourceAdmissible hH P η₀ Z a i n
      (profileWholeDatum M H hH P η₀ Z st hQM hQη z hz src second L alloc
        (fun j=>w j.val) (fun j=>σ j.val) (fun j=>v j.val) (fun j=>θ j.val) hap F p) := by
  intro src U hU hcap hsupport hsmooth hmellin
  let sn := normalizedData hap F p U hU src
  have hplain := normalizedData_plains hap F p U hU src hW₁ hW₂
  have hWP (j : Fin 2) : (![sn.W₁,sn.W₂] j : ℝ→ℂ)=
      ((normalizedPlains hap F p U hU).profile j:ℝ→ℂ) := by
    fin_cases j
    · exact hplain.1
    · exact hplain.2
  have hZp : 0< Z := zero_lt_one.trans hZ
  have hr (j : Fin 2) : 0≤ Real.logb Z (clippedScale (U j))/P.d :=
    div_nonneg (Real.logb_nonneg hZ (clippedScale_ge_one _)) P.hd.le
  have hrbound (j : Fin 2) : Real.logb Z (clippedScale (U j))/P.d≤ P.Rplain := by
    apply (div_le_iff₀ P.hd).mpr
    have hh := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one (U j))) (hcap j)
    rw [Real.logb_rpow hZp hZ.ne'] at hh
    linarith
  have hclip (j : Fin 2) : clippedScale (U j)=(Z^P.d)^(Real.logb Z (clippedScale (U j))/P.d) := by
    rw [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ P.hd.ne',
      Real.rpow_logb hZp hZ.ne' (zero_lt_one.trans_le (clippedScale_ge_one _))]
  refine {
    width := hwidth
    low := whole_high_datum_low M H hH P η₀ Z st hQM hQη z hz sn second L alloc
      (fun j=>w j.val) (fun j=>σ j.val) (fun j=>v j.val) (fun j=>θ j.val)
      (ap/max 1 bp) bp a i hradial hupper
    member := rfl
    upper := hupper
    modulus := hmod
    character := rfl
    mask := hmask.symm
    A := rfl
    height := rfl
    pool := fun j=>hm.pool j.val
    coefficient := fun j I=>common_coefficient hm st.character t C R B j I
    scale := fun j=>hm.scale j.val
    w_nonneg := fun j=>hw j.val
    w_bound := fun j=>hwr j.val
    σ_lower := fun j=>hσlo j.val
    σ_upper := fun j=>hσhi j.val
    slot_frequency := fun j=>hfreq j.val
    slot_height := hslotheight
    plain_frequency := hplainfreq
    plain_height := hplainheight
    W₁ := rfl
    W₂ := rfl
    post_scale := fun _=>rfl
    X_pos := hU
    clipped_scale := hclip
    A_pos := fun _=>div_pos hap (zero_lt_one.trans_le (le_max_left _ _))
    support := ?_
    smooth := ?_
    r_nonneg := hr
    r_bound := hrbound
    mellin₂ := ?_
    mellin_n := ?_
  }
  · intro j
    change Function.support (dilated (![sn.W₁,sn.W₂] j) (clipDilation (U j)))⊆_
    rw [hWP]
    exact hsupport j
  · intro j
    change ContDiff ℝ ∞ (dilated (![sn.W₁,sn.W₂] j) (clipDilation (U j)))
    rw [hWP]
    exact hsmooth j
  · intro j x hx u
    change (1+|u|)^2*‖mellin (dilated (![sn.W₁,sn.W₂] j) (clipDilation (U j)))
      ((x:ℂ)+u*Complex.I)‖≤ P.profileBound 2
    rw [hWP]
    exact hmellin j 2 (Or.inl rfl) x (high_strip_mem ha P.he'.le hx) u
  · intro j x hx u
    change (1+|u|)^(n+2)*‖mellin (dilated (![sn.W₁,sn.W₂] j) (clipDilation (U j)))
      ((x:ℂ)+u*Complex.I)‖≤ P.profileBound (n+2)
    rw [hWP]
    exact hmellin j (n+2) (Or.inr rfl) x (high_strip_mem ha P.he'.le hx) u

/-- Fix the analytic profile budget before choosing the high-source
parameters. Every surviving literal common allocation then satisfies the
profile, conductor and truncated-height gates uniformly. -/
theorem eventual_common_profile_admission {ap bp : ℝ} (hap : 0< ap) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∀n : ℕ,
      ∃F G : Finset (ℕ×ℕ),∃Cprofile : ℝ,(0,0)∈F ∧ 0< Cprofile ∧
      (∀p : Profiles ap bp,∀U : Fin 2→ℝ,∀hU : ∀j,0< U j,
        clippedControl hap F p U hU 0*clippedControl hap F p U hU 1≤ Cprofile*p.control G) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(a t cap : ℝ)(i : ℕ),a≤1 → (i:ℝ)≤ Z^P.τ → cap≤ P.d*P.Rplain →
      ∀{α : Type} [Fintype α] [DecidableEq α],∀(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ v : α→ℝ),
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)
        (st : NaturalState Z P.Bmask P.bΦ)
        (hQM : st.fixedModulus≤ M)(hQη : st.fixedModulus≤η₀.modulus)
        (z : O)(hz : st.radial.keep z),
      st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R*C) →
      st.width≤ P.Mcap → st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 →
      zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture))
        (whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _)
          (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀j,|t+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      |t|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ →
      ∀(second : Bool)(L : Ideal O)
        (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
        (p : Profiles ap bp),
      s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) → s.b₁=bp → s.b₂=bp →
      Cycle61.Physical.sourcePositiveRow
        (commonData (withHeight s st.character t) C R B).toSource second L alloc z≠0 →
      HighSourceAdmissible hH P η₀ Z a i n
        (profileWholeDatum M H hH P η₀ Z st hQM hQη z hz
          (commonData (withHeight s st.character t) C R B) second L alloc
          (fun j=>w j.val) (fun j=>σ j.val) (fun j=>v j.val) (fun j=>θ j.val) hap F p) := by
  obtain ⟨bound,hbound,hnorm⟩ := fixed_clipped_normalization ap bp hap
  refine ⟨bound,hbound,?_⟩
  intro n
  obtain ⟨F,G₀,C₀,hF,hC₀,hprofiles⟩ := hnorm n
  -- The homogeneous control bound holds even for an empty plain support.
  obtain ⟨G,Cprofile,hCprofile,hcontrol⟩ := Cycle61FinalProfiles.clipped_pair_control ap bp hap F
  refine ⟨F,G,Cprofile,hF,hCprofile,hcontrol,?_⟩
  intro P hboundeq hslot hplain η₀
  have hconductor := eventual_whole_source_conductor M H hH η₀ P.bΦ P.Mcap P.Bmask P.margin
    P.hbΦ P.hmargin
  have hheight := eventually_high_truncated_heights P 0 (2*P.τ) hslot hplain (by norm_num)
  filter_upwards [hconductor,hheight] with Z hc hh
  refine ⟨hc.1,?_⟩
  intro a t cap i ha hi hcap α _ _ s θ w σ v hm horiginal C R B st hQM hQη z hz
    hmask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq second L alloc p hW₁ hW₂ hb₁ hb₂ hne
  let src := commonData (withHeight s st.character t) C R B
  let U := profileScales src second L alloc
  have hU := profile_scales_pos src second L alloc
  have hret : ∀j,1≤ U j*bp := by
    have hs := profile_scales_survive src second L alloc z hne
    change 1≤ U 0*s.b₁ ∧ 1≤ U 1*s.b₂ at hs
    rw [hb₁,hb₂] at hs
    intro j
    fin_cases j
    · exact hs.1
    · exact hs.2
  have hp := hprofiles p U hU hret
  have hmod : ((excluded (naturalRow st.character z (st.row_ne_zero z hz)).character
      st.puncture).modulus.absNorm:ℝ)≤ Z^P.d := by
    have hm' := hc.2 st hwidth z (naturalRow st.character z (st.row_ne_zero z hz))
      hradial (Sum.inl ())
    exact hm'.trans (Real.rpow_le_rpow_of_exponent_le hc.1.le P.hdsupply)
  apply actual_common_profile_admissible M H hH P η₀ Z a t hc.1 ha i n s θ w σ v hm
    C R B st hQM hQη hmask z hz hwidth hradial hupper hmod hw hwr hσlo hσhi hfreq
    (hh.2 i hi).1 hplainfreq (hh.2 i hi).2.1 second L alloc hap F p hW₁ hW₂
  · exact actual_common_clipped_scale_cap s C R B st.character t Z cap P.d P.Rplain hc.1.le
      (mul_nonneg P.hd.le P.hRp) hcap horiginal second L alloc
  · exact hp.2.2.1
  · exact hp.2.2.2.1
  · simpa only [hboundeq] using hp.2.2.2.2

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.actual_common_profile_admissible

#print axioms OAI.SevenEighths.Cycle61Moment.actual_common_clipped_scale_cap

#print axioms OAI.SevenEighths.Cycle61Moment.eventual_common_profile_admission

end
/- END ORIGINAL Cycle61.Moment.ProfileCommonAdmissible -/

/- BEGIN ORIGINAL Cycle61.Moment.ProfileJointShellEnergy; sha256 1ed0024bc4d8a69b0b5bdd73810de3761a4982432fb47b03483ebed778fb2e3b -/
section
                                        

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance profileJointFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Residual allocations are contracted at each fixed encoded row; only
then is the joint physical pool counted by the fixed natural dictionary. -/
theorem actual_profile_joint_family_energy {Index Base : Type} [Fintype Index]
    [Fintype Base] (Slots : Index→ Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤ N) (base : Base → Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hloss : 0 < loss) (hε : 0 < ε) {ap bp : ℝ} (hap : 0< ap) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroJointSourceLabel left u₀ unit → Base)
        (holes : NonzeroJointSourceLabel left u₀ unit → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow l).val
          (nonzeroJointSourceRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^m) →
      ∀(F G : Finset (ℕ×ℕ)),(0,0)∈F → ∀Cprofile : ℝ,0≤ Cprofile →
      ∀p : NonzeroJointSourceLabel left u₀ unit→ Profiles ap bp,
      ∀ (S : NonzeroJointSourceLabel left u₀ unit → Index)
        (s : ∀ l, Data (Slots (S l))) (w σ v : ∀ l, Slots (S l) → ℝ)
        (θ : ∀ l, Slots (S l) → RayQuotient.Characters M H)
        (Ds : NonzeroJointSourceLabel left u₀ unit → Finset (Ideal O)),
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧
        (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧ (s l).b₁=bp ∧ (s l).b₂=bp) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, Squarefree L) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, T ≤ (L.absNorm : ℝ) ∧ (L.absNorm : ℝ) < 2*T) →
      (∀ l ∈ labels, ((p l).control G)^2*(wholeControl (s l))^2 ≤ Kcontrol) →
      (∀ l ∈ labels, (s l).toSource.allowance Z+
        Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂] ≤ allowance) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        Cycle61.Physical.sourcePositiveRow (s l).toSource b L alloc (z l)≠0 →
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) hap F (p l))) →
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 0*
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 1≤ Cprofile*(p l).control G) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
          (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*N-
          Cycle61.Physical.sourcePostClip (s l).toSource b Z L alloc ≤ e) →
      (∑ l ∈ labels, ∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤
      C*Cprofile^2*Kcontrol*(1+3*(i+1 : ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨J,Ccount,hCcount,hcount⟩ := actual_whole_joint_high_row_count M H hH
    base η₀ B Q loss hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,Cshell,hCshell,hactual⟩ := actual_profile_high_retained_family M H hH Slots N hN P ε hε hap
  refine ⟨n,Ccount*Cshell,mul_pos hCcount hCshell,?_⟩
  filter_upwards [hactual η₀,eventually_ge_atTop (2 : ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm
    hmissing F G hF Cprofile hCprofile p S s w σ v θ Ds hWsrc hDs hdyad hcontrol hallowance hvalid hprofile hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hTshared : 0 ≤ 3*(i+1 : ℕ)*Z^P.τ := by positivity
  have hcard := hcount left u₀ unit Z hZ₂ q m a (3*(i+1 : ℕ)*Z^P.τ)
    P.Bmask P.bΦ hq ha ha' hTshared labels st hQM hQη z hz
    (fun l => naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l)))
    index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
  let W := Cshell*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpoint (l : NonzeroJointSourceLabel left u₀ unit) (hl : l ∈ labels) :
      (∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤ W := by
    have hr := hZ.2 a (by linarith : 51/100 ≤ a) (by linarith : a ≤ 1) i (S l) (s l)
      (st l) (hQM l) (hQη l) (z l) (hz l) (w l) (σ l) (v l) (θ l)
      F G hF (p l) (hWsrc l hl).1 (hWsrc l hl).2.1 (hWsrc l hl).2.2.1 (hWsrc l hl).2.2.2
      (Ds l) (hDs l hl) T e Cprofile hT hCprofile (fun L hL => (hdyad l hl L hL).1)
      (fun L hL => (hdyad l hl L hL).2) (hvalid l hl) (hprofile l hl) (hexp l hl)
    apply hr.trans
    dsimp [W]
    have he := Real.rpow_le_rpow_of_exponent_le hZ.1.le
      (show e+(s l).toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂]
        ≤ e+allowance by linarith [hallowance l hl])
    calc
      _ = (Cshell*Cprofile^2)*(((p l).control G)^2*(wholeControl (s l))^2)*(2*T)^(2*ε)*
          Z^(e+(s l).toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂]) := by ring
      _ ≤ (Cshell*Cprofile^2)*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcontrol l hl) (by positivity))
            (Real.rpow_nonneg (by positivity) _)
        · exact he
        · positivity
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ _l ∈ labels, W := Finset.sum_le_sum hpoint
    _ = (labels.card : ℝ)*W := by simp [nsmul_eq_mul]
    _ ≤ (Ccount*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
        Z^(m+q*unmarkedDensity (2*a-1)+loss))*W :=
      mul_le_mul_of_nonneg_right hcard hW
    _ = _ := by
      dsimp [W]
      rw [show m+q*unmarkedDensity (2*a-1)+loss+e+allowance =
        (m+q*unmarkedDensity (2*a-1)+loss)+(e+allowance) by ring,
        Real.rpow_add hZp (m+q*unmarkedDensity (2*a-1)+loss) (e+allowance)]
      ring

/-- Residual allocations are contracted at each fixed encoded row; only
then is the joint physical pool counted by the fixed natural dictionary. -/
theorem actual_profile_joint_shell_energy {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base → Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hloss : 0 < loss) (hε : 0 < ε) {ap bp : ℝ} (hap : 0< ap) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroJointSourceLabel left u₀ unit → Base)
        (holes : NonzeroJointSourceLabel left u₀ unit → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow l).val
          (nonzeroJointSourceRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^m) →
      ∀(F G : Finset (ℕ×ℕ)),(0,0)∈F → ∀Cprofile : ℝ,0≤ Cprofile →
      ∀p : NonzeroJointSourceLabel left u₀ unit→ Profiles ap bp,
      ∀ (S : NonzeroJointSourceLabel left u₀ unit → Finset α)
        (s : ∀ l, Data (S l)) (w σ v : ∀ l, S l → ℝ)
        (θ : ∀ l, S l → RayQuotient.Characters M H)
        (Ds : NonzeroJointSourceLabel left u₀ unit → Finset (Ideal O)),
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧
        (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧ (s l).b₁=bp ∧ (s l).b₂=bp) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, Squarefree L) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, T ≤ (L.absNorm : ℝ) ∧ (L.absNorm : ℝ) < 2*T) →
      (∀ l ∈ labels, ((p l).control G)^2*(wholeControl (s l))^2 ≤ Kcontrol) →
      (∀ l ∈ labels, (s l).toSource.allowance Z+
        Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂] ≤ allowance) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        Cycle61.Physical.sourcePositiveRow (s l).toSource b L alloc (z l)≠0 →
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) hap F (p l))) →
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 0*
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 1≤ Cprofile*(p l).control G) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
          (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
          Cycle61.Physical.sourcePostClip (s l).toSource b Z L alloc ≤ e) →
      (∑ l ∈ labels, ∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤
      C*Cprofile^2*Kcontrol*(1+3*(i+1 : ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  exact actual_profile_joint_family_energy M H hH (fun S : Finset α=>↥S)
    (Fintype.card α) (fun S=>by simpa using Finset.card_le_univ S)
    base η₀ B Q loss ε hB hQ hQB hloss hε hap


end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.actual_profile_joint_shell_energy

#print axioms OAI.SevenEighths.Cycle61Moment.actual_profile_joint_family_energy

end
/- END ORIGINAL Cycle61.Moment.ProfileJointShellEnergy -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondHighShell; sha256 049ff4aad1604751a6eb5a912b3c72bf803f29d733959152f7b1eea07dc7e77d -/
section
                                             
                                             
                                     

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Apply the joint density theorem to the literal common-allocated sources.
Normalization, conductor, truncated heights and residual clipping are derived,
with the budget chosen before all live slot subsets and common allocations. -/
theorem actual_common_joint_high_shell {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base→ Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroJointSourceLabel left u₀ unit → Base)
        (holes : NonzeroJointSourceLabel left u₀ unit → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow l).val
          (nonzeroJointSourceRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^m) →
      (i:ℝ)≤ Z^P.τ →
      ∀(S : NonzeroJointSourceLabel left u₀ unit→ Finset α)
        (s : ∀l,Input (S l))
        (E R : NonzeroJointSourceLabel left u₀ unit→ Ideal O)
        (pick : ∀l,actualAllocations (s l).pools (E l))
        (t : NonzeroJointSourceLabel left u₀ unit→ℝ)
        (w σ v : ∀l,S l→ℝ)(θ : ∀l,S l→ RayQuotient.Characters M H)
        (p : NonzeroJointSourceLabel left u₀ unit→ Profiles ap bp)
        (Ds : NonzeroJointSourceLabel left u₀ unit→ Finset (Ideal O)) (cap : ℝ),
      cap≤ P.d*P.Rplain →
      (∀l∈labels,Matches M H hH (s l) η₀ (θ l) (w l) (σ l) (v l) P.Wslot P.B₀ Z) →
      (∀l∈labels,∀second j,Cycle61.Physical.sourcePlainScales (s l).toData.toSource second j≤ Z^cap) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀l∈labels,∀j,0≤ w l j) → (∀l∈labels,∀j,w l j/P.d≤ P.Rwidth) →
      (∀l∈labels,∀j,P.σmin≤σ l j) → (∀l∈labels,∀j,σ l j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v l j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧
        (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧ (s l).b₁=bp ∧ (s l).b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (s l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(wholeControl (src l))^2≤ Kcontrol) →
      (∀l∈labels,(src l).toSource.allowance Z+
        Cycle61.Physical.plainClipAllowance Z ![(src l).b₁,(src l).b₂]≤ allowance) →
      (∀l∈labels,(2*a-1)*Real.logb Z (preVolume (src l))+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤ e) →
      (∑l∈labels,∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))≤
      C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨bound,hbound,hadmit⟩ := eventual_common_profile_admission M H hH hap
  let Slots := fun l : (S : Finset α) × Finset S=>↥l.2
  have hN (l : (S : Finset α) × Finset S) : Fintype.card (Slots l)≤ Fintype.card α := by
    simpa only [Slots,Fintype.card_coe] using
      (Finset.card_le_univ l.2).trans (by simpa using Finset.card_le_univ l.1)
  obtain ⟨J,hjoint⟩ := actual_profile_joint_family_energy M H hH Slots
    (Fintype.card α) hN base η₀ B Q loss ε hB hQ hQB hloss hε hap
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨n,C,hC,henergy⟩ := hjoint P
  obtain ⟨F,G,Cprofile,hF,hCprofile,hprofile,hadmit⟩ := hadmit n
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [henergy,hadmit P hboundeq hslot hplain η₀] with Z he hn
  refine ⟨he.1,?_⟩
  intro left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
    hi S s E R pick t w σ v θ p Ds cap hcap hmatches hscales hstateMask hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hallowance hraw
  apply he.2 left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
    F G hF Cprofile hCprofile.le p
    (fun l=>⟨S l,CenteredMomentCommonProfile.liveIndices (pick l).val⟩) src
    (fun l j=>w l j.val) (fun l j=>σ l j.val) (fun l j=>v l j.val)
    (fun l j=>θ l j.val) Ds hW hDs hdyad hcontrol hallowance
  · intro l hl L hL alloc haL second hne
    exact hn.2 a (t l) cap i (by linarith) hi hcap (s l) (θ l) (w l) (σ l) (v l)
      (hmatches l hl) (hscales l hl) (E l) (R l) (pick l) (st l) (hQM l) (hQη l)
      (z l) (hz l) (hstateMask l hl) (hwidth l hl) (hradial l hl) (hupper l hl)
      (hw l hl) (hwr l hl) (hσlo l hl) (hσhi l hl) (hfreq l hl) (hplainfreq l hl)
      second L alloc (p l) (hW l hl).1 (hW l hl).2.1 (hW l hl).2.2.1 (hW l hl).2.2.2 hne
  · intro l hl L hL alloc haL second
    exact hprofile (p l) _ _
  · intro l hl L hL alloc haL second
    let D := wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
      (src l) second L alloc (fun j=>w l j.val) (fun j=>σ l j.val) (fun j=>v l j.val)
      (fun j=>θ l j.val) ap bp
    have hd := high_source_exponent_le_raw D hn.1
      (fun j=>(hmatches l hl).scale j.val) (fun j=>hw l hl j.val)
      (2*a-1) (by linarith) (by linarith)
    have hr := hraw l hl
    change (2*a-1)*D.total P-Cycle61.Physical.sourcePostClip (src l).toSource second Z L alloc≤
      (2*a-1)*Real.logb Z (preVolume (src l)) at hd
    change (2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
      Cycle61.Physical.sourcePostClip (src l).toSource second Z L alloc≤ e
    linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_joint_high_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondHighShell -/
