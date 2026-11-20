/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Original raw common-profile rows are grouped before their genuine
sixth-free decomposition. The only analytic children are StrongPair finite
energies on actual sixthFreeFiber rows, independent cofactor lengths and
complete surviving whole-slot subsets, including the empty subset.
-/
import Candidate.C092.transport.RawIndependentBall
import Candidate.C092.transport.GroupedPairClassControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet
open ProfileSeparation (commonPair scale pairWeight scale_pos)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local notation "mask₀" => fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameRaw_cef95da131e583f7_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def frameRawRows (s : Finset O) (hne : ∀ z∈s,z≠0) : Finset NonzeroFrequency :=
  s.attach.image (fun z=>⟨z.val,hne z.val z.property⟩)

theorem frameRawRows_sum (s : Finset O) (hne : ∀ z∈s,z≠0) (f : O→ℝ) :
    (∑ z∈frameRawRows s hne,f z.val) = ∑ z∈s,f z := by
  unfold frameRawRows
  have hinj : Function.Injective (fun z : {z // z∈s} => (⟨z.val,hne z.val z.property⟩ : NonzeroFrequency)) := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : NonzeroFrequency => z.val) h
  rw [Finset.sum_image (fun a _ b _ h=>hinj h)]
  exact Finset.sum_attach s f

/-- Every finite original common-row source follows from the actual
independent-character sixth-free leaves. The original keep and complete
raw row set survive; no clean-row hypothesis is imposed before grouping. -/
theorem frame_raw_common_source {ι : Type} [Fintype ι] [DecidableEq ι]
    (rayM : Id) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hsW : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (U M H loss : ℝ),1<U → 0≤M → M≤2 →
    ∀ (η₁ η₂ ηmark base : Character) (θ : ι→RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ)
      (t₁ t₂ tMark Y₁ Y₂ K : ℝ) (J : ℕ) (keep : O→Prop),
      (∀z,keep z→z≠0) → (∀i,0≤w i) → (∀i,0≤σ i) →
      0<Y₁ → 0<Y₂ → 0≤K →
      let mark := fun i z=>normalizedSlot ηmark mask₀ 1 z (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr base θ W U w σ v i) tMark (U^(w i))
      (∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (R:Finset NonzeroFrequency),
        (∀z∈R,keep z.val ∧ rawFrequencyNorm z≤U^M) →
        ∀ B : HeckeInverseAmplification.NonzeroIdeal,(sixthFreeFiber R B).Nonempty →
        ∀ D∈IdealMobiusDivisorSum.idealDivisors B.val,
        ∀ F∈IdealMobiusDivisorSum.idealDivisors B.val,∀ T : Finset ι,
          StrongPair.finiteEnergyOn T (sixthFreeFiber R B) η₁ η₂
            ((commonPair e τ).profile 0) ((commonPair e τ).profile 1) t₁ t₂
            ((scale e.1*Y₁)/(D.absNorm:ℝ)) ((scale e.2*Y₂)/(F.absNorm:ℝ))
            (fun i r=>mark i r.val) ≤ K*pairWeight J τ*
              U^(coreWidth U M B+loss+(5/6)*max 0 (H-coreWidth U M B))) →
      ∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (s:Finset O),
        (∀z∈s,keep z ∧ ‖eisEmbedding z‖^2≤U^M) →
        (∑z∈s,‖GroupedPair.commonRow η₁ η₂ mask₀ 1 1 (fun z=>∏i,mark i z)
          t₁ t₂ Y₁ Y₂ e τ z‖^2) ≤
          C*K*pairWeight J τ*U^(M+loss+(5/6)*max 0 (H-M)+ε) := by
  obtain ⟨C,hC,hraw⟩ := RawIndependentFiber.packed_raw_from_free_classes (ι:=ι)
    rayM Hr hHr W hW hsW ε hε
  refine ⟨C,hC,?_⟩
  intro U M H loss hU hM hM₂ η₁ η₂ ηmark base θ w σ v t₁ t₂ tMark Y₁ Y₂ K J keep
    hkeep hw hσ hY₁ hY₂ hK
  let mark := fun i z=>normalizedSlot ηmark mask₀ 1 z (originalPools rayM Hr 2 U w i)
    (originalCoefficients rayM Hr hHr base θ W U w σ v i) tMark (U^(w i))
  dsimp only
  intro hstrong e τ s hs
  let hn := fun z hz=>hkeep z (hs z hz).1
  let R := frameRawRows s hn
  have hR : ∀z∈R,keep z.val ∧ rawFrequencyNorm z≤U^M := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hh := hs a.val a.property
    exact ⟨hh.1,by simpa only [rawFrequencyNorm,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using hh.2⟩
  have hp₁ := (commonPair e τ).support 0
  have hp₂ := (commonPair e τ).support 1
  have he := hraw U M H loss hU hM hM₂ η₁ η₂ ηmark base θ w σ v
    ((commonPair e τ).profile 0) ((commonPair e τ).profile 1)
    t₁ t₂ tMark (scale e.1*Y₁) (scale e.2*Y₂) (9/4) (9/4) (K*pairWeight J τ) R
    hw hσ (fun x hx=>(hp₁ hx).2) (fun x hx=>(hp₂ hx).2)
    (mul_pos (scale_pos e.1) hY₁) (mul_pos (scale_pos e.2) hY₂)
    (mul_nonneg hK (ProfileSeparation.pairWeight_nonneg J τ))
    (fun z hz=>(hR z hz).2) (hstrong e τ R hR)
  have hid : (∑z∈s,‖GroupedPair.commonRow η₁ η₂ mask₀ 1 1 (fun z=>∏i,mark i z)
      t₁ t₂ Y₁ Y₂ e τ z‖^2) =
      ∑z∈R,(∏i,‖mark i z.val‖^2)*
        ‖original η₁ mask₀ 1 z.val ((commonPair e τ).profile 0) t₁ (scale e.1*Y₁)*
          original η₂ mask₀ 1 z.val ((commonPair e τ).profile 1) t₂ (scale e.2*Y₂)‖^2 := by
    let f : O→ℝ := fun z=>(∏i,‖mark i z‖^2)*
      ‖original η₁ mask₀ 1 z ((commonPair e τ).profile 0) t₁ (scale e.1*Y₁)*
        original η₂ mask₀ 1 z ((commonPair e τ).profile 1) t₂ (scale e.2*Y₂)‖^2
    change _ = ∑z∈frameRawRows s hn,f z.val
    rw [frameRawRows_sum s hn f]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp only [f]
    unfold GroupedPair.commonRow
    rw [GroupedPair.row_eq_original _ _ _ _ _ _ _ _ _ _ _ _ _
      (mul_pos (scale_pos e.1) hY₁) (mul_pos (scale_pos e.2) hY₂)]
    rw [norm_mul,norm_prod,Finset.prod_pow,mul_pow]
    ring
  rw [hid]
  exact he.trans_eq (by ring)

#print axioms frameRawRows_sum
#print axioms frame_raw_common_source
end
end QRH.Cycle092.RegularColoredForward
