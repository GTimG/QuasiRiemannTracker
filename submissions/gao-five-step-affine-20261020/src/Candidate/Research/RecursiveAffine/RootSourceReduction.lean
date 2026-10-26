/- Exact native initial-source reduction at the recursive root ledger.
Original proof Hailey Collet; binding Zhongpai Gao. Apache-2.0. -/
import Candidate.Cycle63.Physical.InitialSourceReduction
import Candidate.Research.RecursiveAffine.RootRawComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
import Candidate.Cycle63.Moment.InitialAffineContract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl

noncomputable local instance recursiveRootReductionLedger : Cycle63.AffineLedger := Cycle153.Root.rootLedger
namespace OAI.SevenEighths.Cycle153RootSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 6000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyOriginalSource
open CenteredMomentCommonRadialData CenteredMomentFirstSourceReduction
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentSourceInputTailUniform CenteredMomentNaturalFixedRaySource
open Cycle63Moment Cycle63FirstActual Cycle63FirstGeometry Cycle63InitialSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentPrimeSlot CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance initialSourceReductionFinite : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

private lemma control_insert {a b : ℝ} (p : Profiles a b) (S : Finset (ℕ×ℕ)) :
    p.control S≤p.control (insert (0,0) S) := by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

/-- Actual initial affine energy reduced to its actual normalized physical mass.
All other terms are proved from the literal .41--.44 initial scales and the
original daughter terminal; no parent-capacity input is used. -/
theorem actual_initial_source_reduction_fixed_mesh {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (anchors : Label→ Character)
    (W : ℝ→ℂ) (aslot bslot lo hi a b bΦ Mmin Mmax ε ξ : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (hlohi : lo≤hi)
    (ha : 0<a) (hlo : a≤1/4) (hhi : 1≤b) (hbΦ : 0<bΦ)
    (hMmin : 0<Mmin) (hMmax : Mmin≤Mmax) (hε : 0<ε) (hξ : 0<ξ)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ 0<comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀j : Label, ∀T : Finset α, ∀θ : T→RayQuotient.Characters rayM H,
    ∀w σ freq : T→ℝ, ∀t height : ℝ,
      (∀i,0≤w i) → (∀i,w i≤ comparisonMesh Mmin Mmax ε) → ∀hσlo : (∀i,lo≤σ i), ∀hσhi : (∀i,σ i≤hi),
      0≤height → (∀i,|freq i|≤height) →
    ∀M Lc : ℝ, Mmin≤M → M≤Mmax →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b, ∀X₁ X₂ : ℝ,
    ∀hX₁ : 0<X₁, ∀hX₂ : 0<X₂,
      Cycle63.AffineLedger.windowBottom*M≤length Z X₁ → Cycle63.AffineLedger.windowBottom*M≤length Z X₂ →
      length Z X₁+length Z X₂+(∑i,w i)≤M → (∑i,w i)≤Cycle63.AffineLedger.slotTop*M →
      ComparisonFits M Lc (length Z X₁) (length Z X₂) (∑i,w i) → ∀hZ : 1<Z, ∀hM : 0≤M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha Lc t X₁ X₂ hX₁ hX₂;
    energy (anchors j) (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp)+
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  have hMax : 0<Mmax := hMmin.trans_le hMmax
  obtain ⟨Ψ,hΨ,hΨpos,D,hD,hred⟩ := uniform_original_reduction (α:=α)
    bΦ bslot a b (Mmax+1) (ε/2) ξ 1 hbΦ hbslot ha (by linarith)
    (by linarith) (by positivity) hξ
  obtain ⟨hmesh,degree,S,hcomp⟩ := actual_fixed_parent_raw_comparison_fixed_mesh rayM H hH anchors
    (Finset.univ:Finset α) W aslot bslot lo hi haslot hWs hW hbslot
    a b bΦ Mmin Mmax ε ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  let mesh := comparisonMesh Mmin Mmax ε
  let G := (CenteredMomentEnergyNaturalInputMatches.profileBound W hW.continuous
    aslot bslot lo hi haslot hWs)^(2*Fintype.card α)
  have hG : 0≤G := pow_nonneg (zero_le_one.trans
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW.continuous
      aslot bslot lo hi haslot hWs)) _
  refine ⟨Ψ,hΨ,hΨpos,hmesh,degree,insert (0,0) S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hcomp η₀ Q hQM hQ0 hQt hQ72
  refine ⟨4*D*G+2*C,by positivity,?_⟩
  filter_upwards [ht,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro j T θ w σ freq t height hw hwmesh hσlo hσhi hheight hfreq M Lc hmin hmax
    Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hn₁ hn₂ hvol hslots hfits hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha Lc t X₁ X₂ hX₁ hX₂
  have hv : CenteredMomentAmplificationChildInput.volume inp≤Z^(Mmax+1) :=
    affine_volume_bound Z M Mmax X₁ X₂ w hZ hM hmax hX₁ hX₂ hvol
  have hred' := hr.2 T inp p rfl rfl (fun _=>le_rfl) 1 s.radial hsΦ hv
    (fixed_inverse_scale_bound Z M Mmax hZ hM hmax)
  have hn₁eq := initial_scale_exact Z X₁ M hZ (hMmin.trans_le hmin) hn₁
  have hn₂eq := initial_scale_exact Z X₂ M hZ (hMmin.trans_le hmin) hn₂
  let we := slotExtend T w 0
  let se := slotExtend T σ lo
  let ve := slotExtend T freq 0
  have hew (i : α) : 0≤we i := by
    dsimp [we,slotExtend]; split_ifs with h
    · exact hw ⟨i,h⟩
    · exact le_rfl
  have hewm (i : α) : we i≤ mesh := by
    dsimp [we,slotExtend]; split_ifs with h
    · exact hwmesh ⟨i,h⟩
    · exact hmesh.le
  have heslo (i : α) : lo≤ se i := by
    dsimp [se,slotExtend]; split_ifs with h
    · exact hσlo ⟨i,h⟩
    · exact le_rfl
  have heshi (i : α) : se i≤hi := by
    dsimp [se,slotExtend]; split_ifs with h
    · exact hσhi ⟨i,h⟩
    · exact hlohi
  have hev (i : α) : |ve i|≤height := by
    dsimp [ve,slotExtend]; split_ifs with h
    · exact hfreq ⟨i,h⟩
    · simpa only [abs_zero] using hheight
  have hesum : (∑i∈T,we i)≤Cycle63.AffineLedger.slotTop*M := by
    rw [←Finset.sum_coe_sort T we]
    simpa only [we,slotExtend_coe] using hslots
  have hfits' : ComparisonFits M Lc (length Z X₁) (length Z X₂) (∑i∈T,we i) := by
    rw [←Finset.sum_coe_sort T we]
    simpa only [we,slotExtend_coe] using hfits
  have hc := hz.2 j M Lc (length Z X₁) (length Z X₂) hmin hmax
    Φ hsΦ hpΦ p T (Finset.subset_univ _) (slotExtend T θ 1) we se ve t height
    hew hewm heslo heshi hheight hev hesum hfits' hZ hM
  simp only [we,se,ve,slotExtend_coe,←hn₁eq,←hn₂eq] at hc
  have hplain : (plainControl inp (p.profile 0) (p.profile 1))^2≤
      G*(p.control (insert (0,0) S))^2 := plain_control_sq_le inp p S (Fintype.card α) _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW.continuous
      aslot bslot lo hi haslot hWs)
    (by simpa using Finset.card_le_univ T) (fun _=>le_rfl)
  have hpc := pow_le_pow_left₀ (p.control_nonneg S) (control_insert p S) 2
  have hdiag := diagonalControl_nonneg Φ
  have hheight1 : 1≤(1+|t|+height)^degree := one_le_pow₀ (by linarith [abs_nonneg t])
  have hpowers : (Z^M)*(Z^(ε/2)+Z^(-(1:ℝ)))≤2*Z^(M+ε) := by
    have hterm (e : ℝ) (he : e≤ε) : Z^M*Z^e≤Z^(M+ε) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    nlinarith [hterm (ε/2) (by linarith),hterm (-1) (by linarith)]
  have hrem : 2*diagonalControl Φ*(D*(plainControl inp (p.profile 0) (p.profile 1))^2*
      (Z^M)*(Z^(ε/2)+Z^(-(1:ℝ))))≤
      4*D*G*diagonalControl Φ*(p.control (insert (0,0) S))^2*
        (1+|t|+height)^degree*Z^(M+ε) := by
    calc
      _ ≤ 2*diagonalControl Φ*(D*(G*(p.control (insert (0,0) S))^2)*
          (2*Z^(M+ε))) := by
        have hh := mul_le_mul (mul_le_mul_of_nonneg_left hplain hD.le) hpowers
          (show 0≤Z^M*(Z^(ε/2)+Z^(-(1:ℝ))) by positivity)
          (show 0≤D*(G*(p.control (insert (0,0) S))^2) by positivity)
        have hh' := mul_le_mul_of_nonneg_left hh
          (show 0≤2*diagonalControl Φ from mul_nonneg (by norm_num) hdiag)
        convert hh' using 1; ring
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right
          (show 0≤4*D*G*diagonalControl Φ*(p.control (insert (0,0) S))^2*Z^(M+ε) by positivity) hheight1
        convert hh using 1 <;> ring
  have hc' := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2 by norm_num)
  have hcomparison : 2*energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ s.radial.keep Φ (Z^M)≤
      2*C*diagonalControl Φ*(p.control (insert (0,0) S))^2*
        (1+|t|+height)^degree*Z^(M+ε) := by
    apply hc'.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpc (mul_nonneg hC.le hdiag))
        (show 0≤(1+|t|+height)^degree by positivity))
      (show 0≤Z^(M+ε) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤2 by norm_num)
    convert hh' using 1; ring
  change _ ≤ 2*diagonalControl Φ*(
      physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp+
      D*(plainControl inp (p.profile 0) (p.profile 1))^2*(Z^M)*(Z^(ε/2)+Z^(-(1:ℝ))))+
    2*energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots
      inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ s.radial.keep Φ (Z^M) at hred'
  apply hred'.trans
  change 2*diagonalControl Φ*(_+_)+_≤_
  rw [mul_add]
  have hh := add_le_add_left (add_le_add hrem hcomparison)
    (2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
      CenteredMomentAmplificationChildInput.volume inp))
  convert hh using 1 <;> ring

end
end OAI.SevenEighths.Cycle153RootSource
#print axioms OAI.SevenEighths.Cycle153RootSource.actual_initial_source_reduction_fixed_mesh
