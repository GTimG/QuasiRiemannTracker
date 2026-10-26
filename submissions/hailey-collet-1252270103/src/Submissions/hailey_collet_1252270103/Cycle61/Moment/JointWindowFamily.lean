import Submissions.hailey_collet_1252270103.Cycle61.Moment.JointWindow

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentPlainWindowEnergy CenteredMomentExceptionalWindowPair
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth FourierBridge
open CenteredMomentSourceRow
open CenteredMomentHeckeWindowEnergy
local notation "O" => HeckeFamily.O
local instance heterogeneousWindowDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- A single Hilbert energy across different surviving slot sets, before
Mellin integration. The scalar normalization is retained for every row. -/
theorem actual_heterogeneous_joint_window_energy {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ) (slots : κ→Finset α) (s : (k : κ)→Input (slots k))
    (C R seed L : κ→Ideal O) (hC : ∀k,Supported (C k)) (η : κ→Character)
    (t θ X : κ→ℝ) (hX : ∀k,0<X k) (z : κ→O) (scalar : κ→ℂ)
    (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀u : ℝ,
      (∑k∈rows,‖scalar k*normalizedColumn
        (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
        (C k) (hC k) (R k) (seed k) (L k) (z k)‖^2)≤E*(1+‖u‖)^(2*J)) :
    (∑k∈rows,‖scalar k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
        E*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  let φ (k : κ) (u : ℝ) := logPhase (θ k-u) (Real.log (X k))*
    (scalar k*normalizedColumn (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
      (C k) (hC k) (R k) (seed k) (L k) (z k))
  have hi (k : κ) : Integrable (fun u=>columnDensity V hc hs u*φ k u) := by
    have hh := (actual_window_column_integrable (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t k) (θ k) (X k) (hX k) V hc hs (z k)).const_mul (scalar k)
    convert hh using 1
    funext u
    dsimp [φ]
    ring
  have hb (u : ℝ) : (∑k : rows,‖φ k.val u‖^2)≤E*((1+‖u‖)^J)^2 := by
    rw [Finset.sum_coe_sort rows (fun k=>‖φ k u‖^2)]
    simpa only [φ,norm_mul,logPhase_norm,one_mul,←pow_mul,Nat.mul_comm] using henergy u
  have hh := finite_weighted_integral_energy (columnDensity V hc hs)
    (fun k : rows=>φ k.val) (fun u=>(1+‖u‖)^J) (fun _=>by positivity)
    E hE (columnDensity_moments V hc hs J) (fun k=>hi k.val) hb
  have he (k : κ) : (∫u : ℝ,columnDensity V hc hs u*φ k u)=
      scalar k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t k) (θ k) (X k) V (z k) := by
    rw [actual_window_column_integral (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t k) (θ k) (X k) (hX k) V hc hs (z k),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [φ]
    ring
  simp only [he] at hh
  rw [Finset.sum_coe_sort rows (fun k=>‖scalar k*windowColumn (s k) (C k) (hC k)
    (R k) (seed k) (L k) (η k) (t k) (θ k) (X k) V (z k)‖^2)] at hh
  exact hh

/-- The second-stage window pair remains joint when different first
allocations retain different subsets of the original slot dictionary. -/
theorem actual_heterogeneous_joint_window_pair {α κ : Type*} [Fintype α] [DecidableEq α]
    (rows : Finset κ) (slots : κ→Finset α) (s v : (k : κ)→Input (slots k))
    (C D R seed L : κ → Ideal O) (hC : ∀ k, Supported (C k))
    (hD : ∀ k, Supported (D k)) (η τ : κ → Character)
    (t₁ t₂ θ₁ θ₂ X Y : κ → ℝ) (hX : ∀ k, 0 < X k) (hY : ∀ k, 0 < Y k)
    (row₁ row₂ : κ → O) (scalar₁ scalar₂ : κ → ℂ)
    (V₁ V₂ : ℝ → ℂ) (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : ContDiff ℝ ∞ V₁) (hs₂ : ContDiff ℝ ∞ V₂)
    (J₁ J₂ : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ u w : ℝ,
      (∑ k ∈ rows,
        ‖scalar₁ k*normalizedColumn
          (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
          (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
        ‖scalar₂ k*normalizedColumn
          (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
          (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖) ≤
      E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :
    (∑ k ∈ rows,
      ‖scalar₁ k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k)‖*
      ‖scalar₂ k*windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k)‖) ≤
      E*(∫ u : ℝ, (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫ w : ℝ, (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖) := by
  let f := fun k : κ => fun u : ℝ => scalar₁ k*
    (columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁ k-u) (Real.log (X k))*
      normalizedColumn (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
        (C k) (hC k) (R k) (seed k) (L k) (row₁ k))
  let g := fun k : κ => fun w : ℝ => scalar₂ k*
    (columnDensity V₂ hc₂ hs₂ w*logPhase (θ₂ k-w) (Real.log (Y k))*
      normalizedColumn (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
        (D k) (hD k) (R k) (seed k) (L k) (row₂ k))
  have hf (k : κ) : Integrable (f k) :=
    (actual_window_column_integrable (s k) (C k) (hC k) (R k) (seed k) (L k)
      (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)).const_mul _
  have hg (k : κ) : Integrable (g k) :=
    (actual_window_column_integrable (v k) (D k) (hD k) (R k) (seed k) (L k)
      (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)).const_mul _
  have hh := paired_integrals rows f g (fun k _ => hf k) (fun k _ => hg k)
    (fun u => (1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun w => (1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun _ => by positivity) (fun _ => by positivity) E hE ?_
  · have hfEq (k : κ) : (∫ u : ℝ, f k u) = scalar₁ k*
        windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
          (η k) (t₁ k) (θ₁ k) (X k) V₁ (row₁ k) := by
      dsimp only [f]
      rw [integral_const_mul, ←actual_window_column_integral
        (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t₁ k) (θ₁ k) (X k) (hX k) V₁ hc₁ hs₁ (row₁ k)]
    have hgEq (k : κ) : (∫ w : ℝ, g k w) = scalar₂ k*
        windowColumn (v k) (D k) (hD k) (R k) (seed k) (L k)
          (τ k) (t₂ k) (θ₂ k) (Y k) V₂ (row₂ k) := by
      dsimp only [g]
      rw [integral_const_mul, ←actual_window_column_integral
        (v k) (D k) (hD k) (R k) (seed k) (L k)
        (τ k) (t₂ k) (θ₂ k) (Y k) (hY k) V₂ hc₂ hs₂ (row₂ k)]
    simpa only [hfEq, hgEq] using hh
  · intro u w
    simp only [f, g, norm_mul, logPhase_norm, mul_one]
    calc
      _ = (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          ∑ k ∈ rows,
            ‖scalar₁ k*normalizedColumn
              (withHeight (s k) (η k) (t₁ k+2*Real.pi*(u-θ₁ k)))
              (C k) (hC k) (R k) (seed k) (L k) (row₁ k)‖*
            ‖scalar₂ k*normalizedColumn
              (withHeight (v k) (τ k) (t₂ k+2*Real.pi*(w-θ₂ k)))
              (D k) (hD k) (R k) (seed k) (L k) (row₂ k)‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [norm_mul, norm_mul]
        ring
      _ ≤ (‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ w‖)*
          (E*(1+‖u‖)^J₁*(1+‖w‖)^J₂) :=
        mul_le_mul_of_nonneg_left (hpair u w) (by positivity)
      _ = _ := by ring

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.actual_heterogeneous_joint_window_pair
#print axioms OAI.SevenEighths.Cycle61Moment.actual_heterogeneous_joint_window_energy
