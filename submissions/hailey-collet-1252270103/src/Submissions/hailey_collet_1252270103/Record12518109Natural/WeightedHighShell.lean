/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from Cycle61.Moment.ProfileShellEnergy, preserving exact profile
normalization, clipping and residual dyad contraction. The literal physical
slot maximum is retained for the independent actual gain supplier. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.WeightedHighRows
import Submissions.hailey_collet_1252270103.Cycle61.Moment.ProfileShellEnergy

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Natural.WeightedHigh
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle61Moment Cycle61HighResidual Cycle61HighProfiles CenteredMomentFiniteProfileExceptional
open Cycle61FinalLow CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance profileShellFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Uniform high-row estimates are applied to normalized profiles; the
original profile control is restored before contracting residual allocations.
Rows killed by their plain support require no analytic admissibility gate. -/
theorem actual_profile_high_retained_weighted_family {Index : Type} [Fintype Index]
    (Slots : Index→Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤N)
    (P : HighSourceParameters) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃ n : ℕ, ∃ C : ℝ, 0<C ∧ ∀η₀ : Character,
      ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      ∀a : ℝ,51/100≤a → a≤1 → ∀i : ℕ,
      ∀l : Index, ∀s : Data (Slots l),
      ∀st : NaturalState Z P.Bmask P.bΦ,
      ∀(hQM : st.fixedModulus≤M)(hQη : st.fixedModulus≤η₀.modulus)
        (z : O)(hz : st.radial.keep z),
      ∀(w σ v : Slots l→ℝ)(θ : Slots l→RayQuotient.Characters M H),
      ∀(F G : Finset (ℕ×ℕ)), (0,0)∈F → ∀p : Profiles ap bp,
      s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) → s.b₁=bp → s.b₂=bp →
      ∀Ds : Finset (Ideal O), (∀L∈Ds,Squarefree L) →
      ∀T e Cprofile : ℝ,1≤T → 0≤Cprofile →
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
        (2*a-1)*((wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
          s b L alloc w σ v θ ap bp).total P-(∑j∈liveIndices L alloc,w j))+
          2*P.εplain*P.d-
          Cycle61.Physical.sourcePostClip s.toSource b Z L alloc≤e) →
      (∑L∈Ds,∑alloc∈s.toSource.active L,retainedAllocationCost s L alloc z) ≤
        C*Cprofile^2*(p.control G)^2*(wholeControl s)^2*(2*T)^(2*ε)*
          Z^(e+s.toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂])*
          sourceSlotMaximum s z := by
  obtain ⟨n,Cp,hCp,hactual⟩ := actual_high_source_datum_weighted M H hH P
  have he (l : Index) := retained_pair_shell N (hN l) (hN l) ε hε
  choose Cshell hCshell hsh using he
  let Csh := 1+∑l,Cshell l
  have hCsh : 0<Csh := by
    dsimp [Csh]
    have := Finset.sum_nonneg (fun l (_ : l∈Finset.univ)=>(hCshell l).le)
    linarith
  have hshell (l : Index) : RetainedPairShellBound (Slots l) (Slots l) Csh ε := by
    apply (hsh l).mono
    have hh := Finset.single_le_sum (fun k (_ : k∈Finset.univ)=>(hCshell k).le)
      (Finset.mem_univ l)
    dsimp [Csh]
    linarith
  let K := Cp^2
  have hK : 0<K := sq_pos_of_pos hCp
  refine ⟨n,4*K*Csh,by positivity,?_⟩
  intro η₀
  filter_upwards [hactual] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i l s st hQM hQη z hz w σ v θ F G hF p hW₁ hW₂ hb₁ hb₂
    Ds hDs T e Cprofile hT hCprofile hlo hhi hvalid hcontrol hexp
  have hZp : 0<Z := zero_lt_one.trans hZ.1
  let Kp := Cprofile^2*(p.control G)^2*K
  have hKp : 0≤Kp := by dsimp [Kp]; positivity
  have hslotmax := sourceSlotMaximum_nonneg s z
  have hpoint (L : Ideal O) (hL : L∈Ds)
      (alloc : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2)))
      (halloc : alloc∈s.toSource.active L) (b : Bool) :
      (normalizedPositiveNorm s.toSource b Z L alloc z)^2≤(Kp*sourceSlotMaximum s z)*Z^e := by
    by_cases hn : Cycle61.Physical.sourcePositiveRow s.toSource b L alloc z=0
    · simp only [normalizedPositiveNorm,hn,norm_zero,zero_div,zero_pow (by norm_num : 2≠0)]
      positivity
    let D := profileWholeDatum M H hH P η₀ Z st hQM hQη z hz s b L alloc w σ v θ hap F p
    have hc := hZ.2 η₀ a ha ha' i D (hvalid L hL alloc halloc b hn)
    have hmax : sourceSlotMaximum D.source D.z=sourceSlotMaximum s z := rfl
    rw [hmax] at hc
    have hret : ∀j,1≤profileScales s b L alloc j*bp := by
      have hh := profile_scales_survive s b L alloc z hn
      rw [hb₁,hb₂] at hh
      intro j; fin_cases j
      · exact hh.1
      · exact hh.2
    have hr := sourcePositiveRow_normalized_bound hap F hF p _ (profile_scales_pos s b L alloc)
      hret s hW₁ hW₂ b L alloc z G Cprofile
      (K*Z^((2*a-1)*(D.total P-(∑j∈liveIndices L alloc,w j))+2*P.εplain*P.d)*sourceSlotMaximum s z)
      hCprofile (hcontrol L hL alloc halloc b) hc
    have hp := normalizedPositiveNorm_sq_bound s.toSource b Z hZp L alloc z (Kp*sourceSlotMaximum s z)
      ((2*a-1)*(D.total P-(∑j∈liveIndices L alloc,w j))+2*P.εplain*P.d)
      (hr.trans_eq (by dsimp [Kp]; ring))
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hKp (sourceSlotMaximum_nonneg s z))
    apply Real.rpow_le_rpow_of_exponent_le hZ.1.le
    exact hexp L hL alloc halloc b
  have hpairs (L : Ideal O) (hL : L∈Ds)
      (x : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2))) (hx : x∈s.toSource.active L)
      (y : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2))) (hy : y∈s.toSource.active L)
      (b c : Bool) : normalizedPositiveNorm s.toSource b Z L x z*
        normalizedPositiveNorm s.toSource c Z L y z≤(Kp*sourceSlotMaximum s z)*Z^e := by
    have hhx := hpoint L hL x hx b
    have hhy := hpoint L hL y hy c
    nlinarith [sq_nonneg (normalizedPositiveNorm s.toSource b Z L x z-
      normalizedPositiveNorm s.toSource c Z L y z)]
  have hbound := hshell l s s Ds hDs (fun _ _ _=>z) (fun _ _ _=>z) T Z
    hT hZ.1 hlo hhi (fun _ _=>(Kp*sourceSlotMaximum s z)*Z^e) (fun _ _=>by positivity) hpairs
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


end
end OAI.SevenEighths.Record12518109Natural.WeightedHigh
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.actual_profile_high_retained_weighted_family
