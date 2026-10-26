/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite positive projected initial rows enter their literal marked physical mass. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialProjectedDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledInitialEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.High.CoupledFirst QRH.Record1252270103Source.High.CoupledInitial
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def markedFiniteEnergy (s : Input ι) (R : Ideal O) (A : O) (b X₁ X₂ : ℝ)
    (rows : Finset O) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑z∈rows,if keep z then
    ‖markedPositiveRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b s.slots
      (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t X₁ X₂‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0

theorem marked_initial_finite_centering (s : Input ι) (R : Ideal O) (A : O)
    (b : ℝ) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b)
    (rows : Finset O) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀x,0≤(Φ x).re) :
    markedFiniteEnergy s R A b s.X₁ s.X₂ rows keep Φ K≤
      2*((∑z∈rows,if keep z then
        ‖firstNormalizedRow s (markedSourceModifier 1 1 1 1 (fun _=>1)) R A z‖^2*
          (Φ (‖eisEmbedding z‖^2/K)).re else 0)+
        markedFiniteEnergy s R A b s.Y₁ s.Y₂ rows keep Φ K) := by
  unfold markedFiniteEnergy
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  by_cases hk : keep z
  · simp only [hk,ite_true]
    have h:=mul_le_mul_of_nonneg_right (norm_sq_center_le
      (markedPositiveRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b s.slots
        (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.X₁ s.X₂)
      (markedPositiveRow s.η (fixedBadMask*idealGenerator R) A z s.W₁ s.W₂ b s.slots
        (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P s.t s.Y₁ s.Y₂)) (hΦ (‖eisEmbedding z‖^2/K))
    rw [marked_initial_row_difference s R A z b hb₁ hb₂] at h
    nlinarith only [h]
  · simp only [hk,ite_false,add_zero,mul_zero,le_refl]

/-- Actual projected initial energy is bounded by the actual marked first
physical mass, its checked diagonal/tail terms, and the same projected reference. -/
theorem marked_initial_finite_first_physical (hi : ι→ℝ) (wlo whi B ε ξ saving : ℝ)
    (hhi : ∀i,0≤hi i) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B)
    (hε : 0<ε) (hξ : 0<ξ) :
    ∃Sdiag Stail : Finset (ℕ×ℕ),∃Cdiag Ctail : ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀(s : Input ι)(W₁ W₂ : 𝓢(ℝ,ℂ)),
      s.W₁=W₁ →s.W₂=W₂ →Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi →(∀i,s.hi i≤hi i) →
      ∀(R : Ideal O)(A : O)(b : ℝ),s.b₁≤b →s.b₂≤b →
      ∀(rows : Finset O)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),
      0<K →(∀x,0≤(Φ x).re) →volume s.toData≤Z^B →K⁻¹≤Z^B →
      markedFiniteEnergy s R A b s.X₁ s.X₂ rows keep Φ K≤
      2*(physicalMass s (markedSourceModifier 1 1 1 1 (fun _=>1)) R 1
          (fixedBadMask*idealGenerator R) A Φ K Z ξ/volume s.toData+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving)+
        markedFiniteEnergy s R A b s.Y₁ s.Y₂ rows keep Φ K) := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,h⟩ := finite_first_physical_reduction hi wlo whi B ε ξ saving
    hhi hwlo hwhi hB hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R A b hb₁ hb₂ rows keep Φ K hK hΦ hV hKi
  have hc:=marked_initial_finite_centering s R A b hb₁ hb₂ rows keep Φ K hΦ
  have hp:=hZ.2 s (markedSourceModifier 1 1 1 1 (fun _=>1)) W₁ W₂
    (fun v _=>marked_modifier_norm v) he₁ he₂ hs₁ hs₂ hshi R A rows keep Φ K hK hΦ hV hKi
  exact hc.trans (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) (by norm_num))

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.marked_initial_finite_centering
#print axioms QRH.Record1252270103Low.marked_initial_finite_first_physical
