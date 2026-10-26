import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ProfileShellEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.HighParameters
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceConductor
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceDatum
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open CenteredMomentFiniteProfileExceptional Cycle63HighProfiles Cycle63FinalLow
open ConcreteTraceCRT HeckeDetectorZeros
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
      Cycle63.Physical.sourcePlainScales s.toData.toSource second j := by
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
    (τ : Character) (t Z cap d Rp : ℝ) (hZ : 1≤Z) (hdRp : 0≤d*Rp)
    (hcap : cap≤d*Rp)
    (horiginal : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (j : Fin 2) :
    clippedScale (profileScales (commonData (withHeight s τ t) C R B) second L alloc j)≤Z^(d*Rp) := by
  apply max_le (Real.one_le_rpow hZ hdRp)
  exact (common_profile_scale_le s C R B τ t second L alloc j).trans
    ((horiginal second j).trans (Real.rpow_le_rpow_of_exponent_le hZ hcap))

/-- Admissibility of the actual common-allocated source. Slot coefficients
come from the original ray dictionary, and plain bounds come from the
uniform clipped normalization. Only geometric and height gates remain. -/
theorem actual_common_profile_admissible {α : Type} [Fintype α] [DecidableEq α]
    (P : HighSourceParameters) (η₀ : Character) (Z a t : ℝ) (hZ : 1<Z) (ha : a≤1)
    (i n : ℕ) (s : Input α) (θ : α→RayQuotient.Characters M H) (w σ v : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z)
    (C R : Ideal O) (B : actualAllocations s.pools C)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (hmask : st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*
      ConcretePrimeRowBridge.idealGenerator (R*C))
    (z : O) (hz : st.radial.keep z)
    (hwidth : st.width≤P.Mcap)
    (hradial : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0)
    (hupper : zeroMaximum
      (wholeSourceFamily M H hH η₀
        (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture))
      (whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _)
        (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e)
    (hmod : ((excluded (naturalRow st.character z (st.row_ne_zero z hz)).character
      st.puncture).modulus.absNorm:ℝ)≤Z^P.d)
    (hw : ∀j,0≤w j) (hwr : ∀j,w j/P.d≤P.Rwidth)
    (hσlo : ∀j,P.σmin≤σ j) (hσhi : ∀j,σ j≤P.σmax)
    (hfreq : ∀j,|t+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)
    (hslotheight : (3+(3*i+2:ℕ)*Z^P.τ)^2≤(Z^P.d)^P.vslot)
    (hplainfreq : |t|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)
    (hplainheight : (3+(3*i+2:ℕ)*Z^P.τ)^4≤(Z^P.d)^P.vplain)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    {ap bp : ℝ} (hap : 0<ap) (F : Finset (ℕ×ℕ)) (p : Profiles ap bp)
    (hW₁ : s.W₁=(p.profile 0:ℝ→ℂ)) (hW₂ : s.W₂=(p.profile 1:ℝ→ℂ)) :
    let src := commonData (withHeight s st.character t) C R B
    let U := profileScales src second L alloc
    let hU := profile_scales_pos src second L alloc
    (∀j,clippedScale (U j)≤Z^(P.d*P.Rplain)) →
    (∀j,Function.support (dilated ((normalizedPlains hap F p U hU).profile j)
      (clipDilation (U j)))⊆Icc (ap/max 1 bp) bp) →
    (∀j,ContDiff ℝ ∞ (dilated ((normalizedPlains hap F p U hU).profile j)
      (clipDilation (U j)))) →
    (∀j k,(k=2 ∨ k=n+2) → ∀x∈Icc (-1:ℝ) 2,∀u : ℝ,
      (1+|u|)^k*‖mellin (dilated ((normalizedPlains hap F p U hU).profile j)
        (clipDilation (U j))) ((x:ℂ)+u*Complex.I)‖≤P.profileBound k) →
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
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hr (j : Fin 2) : 0≤Real.logb Z (clippedScale (U j))/P.d :=
    div_nonneg (Real.logb_nonneg hZ (clippedScale_ge_one _)) P.hd.le
  have hrbound (j : Fin 2) : Real.logb Z (clippedScale (U j))/P.d≤P.Rplain := by
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
      ((x:ℂ)+u*Complex.I)‖≤P.profileBound 2
    rw [hWP]
    exact hmellin j 2 (Or.inl rfl) x (high_strip_mem ha P.he'.le hx) u
  · intro j x hx u
    change (1+|u|)^(n+2)*‖mellin (dilated (![sn.W₁,sn.W₂] j) (clipDilation (U j)))
      ((x:ℂ)+u*Complex.I)‖≤P.profileBound (n+2)
    rw [hWP]
    exact hmellin j (n+2) (Or.inr rfl) x (high_strip_mem ha P.he'.le hx) u

/-- Fix the analytic profile budget before choosing the high-source
parameters. Every surviving literal common allocation then satisfies the
profile, conductor and truncated-height gates uniformly. -/
theorem eventual_common_profile_admission {ap bp : ℝ} (hap : 0<ap) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∀n : ℕ,
      ∃F G : Finset (ℕ×ℕ),∃Cprofile : ℝ,(0,0)∈F ∧ 0<Cprofile ∧
      (∀p : Profiles ap bp,∀U : Fin 2→ℝ,∀hU : ∀j,0<U j,
        clippedControl hap F p U hU 0*clippedControl hap F p U hU 1≤Cprofile*p.control G) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(a t cap : ℝ)(i : ℕ),a≤1 → (i:ℝ)≤Z^P.τ → cap≤P.d*P.Rplain →
      ∀{α : Type} [Fintype α] [DecidableEq α],∀(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ),
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)
        (st : NaturalState Z P.Bmask P.bΦ)
        (hQM : st.fixedModulus≤M)(hQη : st.fixedModulus≤η₀.modulus)
        (z : O)(hz : st.radial.keep z),
      st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R*C) →
      st.width≤P.Mcap → st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 →
      zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture))
        (whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e →
      (∀j,0≤w j) → (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀j,|t+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      |t|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ →
      ∀(second : Bool)(L : Ideal O)
        (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
        (p : Profiles ap bp),
      s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) → s.b₁=bp → s.b₂=bp →
      Cycle63.Physical.sourcePositiveRow
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
  obtain ⟨G,Cprofile,hCprofile,hcontrol⟩ := Cycle63FinalProfiles.clipped_pair_control ap bp hap F
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
  have hret : ∀j,1≤U j*bp := by
    have hs := profile_scales_survive src second L alloc z hne
    change 1≤U 0*s.b₁ ∧ 1≤U 1*s.b₂ at hs
    rw [hb₁,hb₂] at hs
    intro j
    fin_cases j
    · exact hs.1
    · exact hs.2
  have hp := hprofiles p U hU hret
  have hmod : ((excluded (naturalRow st.character z (st.row_ne_zero z hz)).character
      st.puncture).modulus.absNorm:ℝ)≤Z^P.d := by
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
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
