import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionRawOrdinary
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionRawRescale
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionRawSlots
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open LocalMoment
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- Actual oriented zero rows inherit any small-root marked estimate.
The large-root estimate, exceptional cores, summation, and height losses
are discharged by the verified ordinary density and sixth-power lift. -/
theorem actual_marked_raw_from_small_roots {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss tailε : ℝ)
    (hloss : 0<loss) (htailε : 0<tailε) (htailmax : tailε≤5/7) :
    ∃J₀ : ℕ,∃C₀ D₀ : ℝ,0<C₀ ∧ 0<D₀ ∧
      ∀(J : ℕ)(C : ℝ),0≤C → ∀(reverse : Label→Bool)(a T U κ A gain : ℝ),
      4/5≤a → a≤7/8 → 0≤T → 1≤U → 0≤κ →
      ∀(R : Finset NonzeroFrequency)(f : NonzeroFrequency→ℝ),
      (∀u∈R,rawFrequencyNorm u≤U ∧ orientedActualZeroRow D.data reverse a T u) →
      (∀u∈R,f u≤U^A) →
      (∀B : NZIdeal,(B.val.absNorm : ℝ)≤U^κ →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          (C*(1+T)^J)*U^(A-gain)*(U/(B.val.absNorm : ℝ)^6)^(unmarkedDensity (2*a-1)+loss)) →
      (∑u∈R,f u) ≤ (C+C₀)*D₀*(1+T)^(J+J₀)*
        U^(unmarkedDensity (2*a-1)+loss+A-
          min gain (κ*(6*(unmarkedDensity (2*a-1)+loss)-1-tailε))) := by
  obtain ⟨J₀,C₀,hC₀,hordinary⟩ := actual_ordinary_weighted_fibers D loss hloss
  obtain ⟨D₀,hD₀,hlift⟩ := raw_marked_split_lift tailε htailε
  refine ⟨J₀,C₀,D₀,hC₀,hD₀,?_⟩
  intro J C hC reverse a T U κ A gain ha ha' hT hU hκ R f hR hf hsmall
  let ρ := unmarkedDensity (2*a-1)+loss
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hbase : 1≤1+T := by linarith
  have hρ : 1+tailε≤6*ρ := by
    dsimp [ρ]
    have hh := unmarkedDensity_ge_two_sevenths (show 2*a-1≤3/4 by linarith)
    linarith
  have hheight₁ : C*(1+T)^J≤(C+C₀)*(1+T)^(J+J₀) := by
    apply (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₀.le) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.le_add_right J J₀))
      (add_nonneg hC hC₀.le)
  have hheight₀ : C₀*(1+T)^J₀≤(C+C₀)*(1+T)^(J+J₀) := by
    apply (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.le_add_left J₀ J))
      (add_nonneg hC hC₀.le)
  have hh := hlift U ((C+C₀)*(1+T)^(J+J₀)) ρ κ A gain hU (by positivity) hκ hρ R f
    (fun B hB=>(hsmall B hB).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hheight₁ (Real.rpow_nonneg hUp.le _))
        (Real.rpow_nonneg (by positivity) _)))
    (fun B _=>(hordinary reverse a T U (U^A) ha ha' hT hUp
      (Real.rpow_nonneg hUp.le _) R f hR hf B).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hheight₀ (Real.rpow_nonneg hUp.le _))
        (Real.rpow_nonneg (by positivity) _)))
  convert hh using 1
  dsimp [ρ]
  ring

end
end OAI.SevenEighths.Deletion26

end Record1252270103Bootstrap.PR67
