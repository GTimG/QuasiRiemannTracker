import Candidate.Cycle63.Moment.ProfileShellEnergy
import Candidate.Cycle63.Marked.HighFullSlotEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle63HighResidual Cycle63HighProfiles CenteredMomentFiniteProfileExceptional
open Cycle63FinalLow CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentPrimeSlot
open CenteredMomentNaturalFixedRaySource HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def retainedSourceSlotWeight {ι : Type} [Fintype ι]
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (st : NaturalState Z P.Bmask P.bΦ) (z : O) (hz : st.radial.keep z)
    (w σ v : ι→ℝ) (θ : ι→RayQuotient.Characters M H) (t : ℝ) : ℝ :=
  ∏k,(max 1 ‖naturalSlot (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
    (primePool M H P.B₀ (Z^(w k)))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight P.Wslot (Z^(w k)) (σ k) (v k) I) t) (Z^(w k))‖)^2

/-- Contract all residual allocations while retaining the joint full slot
weight at the actual row. The remaining exponent contains only the two
plain widths; it is independent of residual frozen/live choices. -/
theorem actual_profile_marked_retained_family {Index : Type} [Fintype Index]
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
        Cycle63.Physical.sourcePositiveRow s.toSource b L alloc z≠0 →
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z st hQM hQη z hz s b L alloc w σ v θ hap F p)) →
      (∀L∈Ds,∀alloc∈s.toSource.active L,∀b : Bool,
        clippedControl hap F p (profileScales s b L alloc) (profile_scales_pos s b L alloc) 0*
          clippedControl hap F p (profileScales s b L alloc) (profile_scales_pos s b L alloc) 1≤
          Cprofile*p.control G) →
      ((2*a-1)*(Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s)-∑k,w k)+
        2*P.εplain*P.d≤e) →
      (∑L∈Ds,∑alloc∈s.toSource.active L,retainedAllocationCost s L alloc z) ≤
        C*Cprofile^2*(p.control G)^2*(wholeControl s)^2*(2*T)^(2*ε)*
          Z^(e+s.toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![s.b₁,s.b₂])*
          retainedSourceSlotWeight M H hH P η₀ Z st z hz w σ v θ s.t := by
  obtain ⟨n,Cp,hCp,hactual⟩ := actual_high_source_factored (M:=M) (H:=H) hH P
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
  let wt := retainedSourceSlotWeight M H hH P η₀ Z st z hz w σ v θ s.t
  have hwt : 0≤wt := Finset.prod_nonneg (fun _ _=>sq_nonneg _)
  let Kp := Cprofile^2*(p.control G)^2*K*wt
  have hKp : 0≤Kp := by dsimp [Kp]; positivity
  have hpoint (L : Ideal O) (hL : L∈Ds)
      (alloc : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2)))
      (halloc : alloc∈s.toSource.active L) (b : Bool) :
      (normalizedPositiveNorm s.toSource b Z L alloc z)^2≤Kp*Z^e := by
    by_cases hn : Cycle63.Physical.sourcePositiveRow s.toSource b L alloc z=0
    · simp only [normalizedPositiveNorm,hn,norm_zero,zero_div,zero_pow (by norm_num : 2≠0)]
      positivity
    let D := profileWholeDatum M H hH P η₀ Z st hQM hQη z hz s b L alloc w σ v θ hap F p
    have hD:=hvalid L hL alloc halloc b hn
    have hc₀:=hZ.2 η₀ a ha ha' i D hD
    have hc:=high_source_row_full_slot_envelope hH D hZ.1 hD.scale (2*a-1) K
      (2*P.εplain*P.d) (by linarith) (by linarith) hK.le hc₀
    change ‖Cycle63.Physical.sourcePositiveRow
      (normalizedData hap F p (profileScales s b L alloc)
        (profile_scales_pos s b L alloc) s).toSource b L alloc z‖^2≤
        (K*wt)*Z^((2*a-1)*(Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s)-∑k,w k)+
          2*P.εplain*P.d+Cycle63.Physical.sourcePostClip s.toSource b Z L alloc) at hc
    have hcap : ‖Cycle63.Physical.sourcePositiveRow
      (normalizedData hap F p (profileScales s b L alloc)
        (profile_scales_pos s b L alloc) s).toSource b L alloc z‖^2≤
        (K*wt)*Z^(e+Cycle63.Physical.sourcePostClip s.toSource b Z L alloc) := by
      apply hc.trans
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.1.le
        (by linarith)) (mul_nonneg hK.le hwt)
    have hret : ∀j,1≤profileScales s b L alloc j*bp := by
      have hh := profile_scales_survive s b L alloc z hn
      rw [hb₁,hb₂] at hh
      intro j; fin_cases j
      · exact hh.1
      · exact hh.2
    have hr := sourcePositiveRow_normalized_bound hap F hF p _ (profile_scales_pos s b L alloc)
      hret s hW₁ hW₂ b L alloc z G Cprofile
      ((K*wt)*Z^(e+Cycle63.Physical.sourcePostClip s.toSource b Z L alloc))
      hCprofile (hcontrol L hL alloc halloc b) hcap
    have hp := normalizedPositiveNorm_sq_bound s.toSource b Z hZp L alloc z Kp
      (e+Cycle63.Physical.sourcePostClip s.toSource b Z L alloc)
      (hr.trans_eq (by dsimp [Kp];ring))
    simpa only [add_sub_cancel_right] using hp
  have hpairs (L : Ideal O) (hL : L∈Ds)
      (x : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2))) (hx : x∈s.toSource.active L)
      (y : Allocation L (Finset.univ : Finset (Slots l⊕Fin 2))) (hy : y∈s.toSource.active L)
      (b c : Bool) : normalizedPositiveNorm s.toSource b Z L x z*
        normalizedPositiveNorm s.toSource c Z L y z≤Kp*Z^e := by
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
      rw [show e+s.toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![s.b₁,s.b₂] =
        e+(s.toSource.allowance Z+s.toSource.allowance Z+
          Cycle63.Physical.plainClipAllowance Z ![s.b₁,s.b₂]+
          Cycle63.Physical.plainClipAllowance Z ![s.b₁,s.b₂])/2 by ring,
        Real.rpow_add hZp]
      dsimp [Kp,wt]
      ring)

end
end OAI.SevenEighths.Cycle63Moment
#print axioms OAI.SevenEighths.Cycle63Moment.actual_profile_marked_retained_family
