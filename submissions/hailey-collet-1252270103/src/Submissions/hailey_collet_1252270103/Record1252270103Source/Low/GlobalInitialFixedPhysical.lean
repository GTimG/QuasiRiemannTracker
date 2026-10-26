/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed radial majorant removes moving radial seminorms from the physical inlet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialProjectedPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSourceMass QuadraticInitialBound CenteredMomentEnergyFixedRadialSource
open OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O"=>HeckeFamily.O

/-- Chosen only from the fixed radial support bound, independent of slot type,
mesh, characters, profiles, heights and scales. -/
def initialRadialBump (bΦ : ℝ) (hbΦ : 0<bΦ) : 𝓢(ℝ,ℂ) :=
  Classical.choose (fixed_source bΦ hbΦ)

theorem initialRadialBump_contract (bΦ : ℝ) (hbΦ : 0<bΦ) :
    Function.support (initialRadialBump bΦ hbΦ:ℝ → ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(initialRadialBump bΦ hbΦ x).re) ∧
      ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ → ℂ)⊆Set.Iic bΦ →
      ∀(η : Character)(m A : O)(t : ℝ)(S : Finset (Ideal O))(c : Ideal O → ℂ)(K : ℝ),0<K →
      ‖finiteHeckeEnergy η m A t S c Φ K‖≤
        diagonalControl Φ*‖finiteHeckeEnergy η m A t S c (initialRadialBump bΦ hbΦ) K‖ :=
  Classical.choose_spec (fixed_source bΦ hbΦ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The reference term keeps the original radial profile; only the centered
finite norm enters the fixed smooth physical mass. -/
theorem marked_initial_fixed_first_physical (bΦ : ℝ) (hbΦ : 0<bΦ)
    (hi : ι → ℝ) (wlo whi B ε ξ saving : ℝ)
    (hhi : ∀i,0≤hi i) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B)
    (hε : 0<ε) (hξ : 0<ξ) :
    ∃Sdiag Stail : Finset (ℕ×ℕ),∃Cdiag Ctail : ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀(s : Input ι)(W₁ W₂ : 𝓢(ℝ,ℂ)),
      s.W₁=W₁ → s.W₂=W₂ → Function.support (W₁:ℝ → ℂ)⊆Set.Icc wlo whi →
      Function.support (W₂:ℝ → ℂ)⊆Set.Icc wlo whi → (∀i,s.hi i≤hi i) →
      ∀(R : Ideal O)(A : O)(b : ℝ),s.b₁≤b → s.b₂≤b →
      ∀(rows : Finset O)(keep : O → Prop)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),
      0<K → (∀x,0≤(Φ x).re) → Function.support (Φ:ℝ → ℂ)⊆Set.Iic bΦ →
      volume s.toData≤Z^B → K⁻¹≤Z^B →
      markedFiniteEnergy s R A b s.X₁ s.X₂ rows keep Φ K≤
      2*diagonalControl Φ*(
        physicalMass s (markedSourceModifier 1 1 1 1 (fun _=>1)) R 1
          (fixedBadMask*idealGenerator R) A (initialRadialBump bΦ hbΦ) K Z ξ/volume s.toData+
        Cdiag*(plainControl s W₁ W₂)^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) (initialRadialBump bΦ hbΦ)*K*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) (initialRadialBump bΦ hbΦ)*K*Z^(-saving))+
        2*markedFiniteEnergy s R A b s.Y₁ s.Y₂ rows keep Φ K := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,h⟩:=original_first_physical_reduction hi wlo whi B ε ξ saving
    hhi hwlo hwhi hB hε hξ
  have hbump:=initialRadialBump_contract bΦ hbΦ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R A b hb₁ hb₂ rows keep Φ K hK hΦ hsΦ hV hKi
  have hp:=hZ.2 s (markedSourceModifier 1 1 1 1 (fun _=>1)) 1 W₁ W₂ zero_le_one
    (fun v _=>marked_modifier_norm v) he₁ he₂ hs₁ hs₂ hshi
    (fixedBadMask*idealGenerator R) A ((dvd_mul_right goodLambda 2).trans (dvd_mul_right _ _))
    ((dvd_mul_left (2:O) goodLambda).trans (dvd_mul_right _ _)) R 1
    (initialRadialBump bΦ hbΦ) K hK hV hKi
  simp only [one_mul] at hp
  have hdom:=div_le_div_of_nonneg_right
    (hbump.2.2 Φ hsΦ s.η (fixedBadMask*idealGenerator R) A s.t
      (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s (markedSourceModifier 1 1 1 1 (fun _=>1)) R 1) K hK) (volume_pos s).le
  rw [mul_div_assoc] at hdom
  have hfinite:=finite_first_normalized_le_full s
    (markedSourceModifier 1 1 1 1 (fun _=>1)) R A rows keep Φ K hK hΦ
  have hc:=marked_initial_finite_centering s R A b hb₁ hb₂ rows keep Φ K hΦ
  have hb:=hfinite.trans (hdom.trans (mul_le_mul_of_nonneg_left hp (diagonalControl_nonneg Φ)))
  calc
    _≤2*(diagonalControl Φ*(_+_+_)+markedFiniteEnergy s R A b s.Y₁ s.Y₂ rows keep Φ K) :=
      hc.trans (mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) (by norm_num))
    _=_ := by ring

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.initialRadialBump_contract
#print axioms QRH.Record1252270103Low.marked_initial_fixed_first_physical
