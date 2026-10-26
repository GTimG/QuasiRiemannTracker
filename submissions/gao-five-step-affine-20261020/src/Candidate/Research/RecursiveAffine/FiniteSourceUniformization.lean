/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153SourceUniform
noncomputable section
open scoped Classical BigOperators
open Filter

/-- Metadata are selected on the finite ORIGINAL carrier, before moving
Z and before selecting a surviving subset. The sums avoid a nonemptiness
assumption, so the empty original carrier is covered as well. -/
def uniformDegree {I : Type} [Fintype I] (d : I→ℕ) : ℕ:=∑i,d i

def uniformControl {I : Type} [Fintype I] (S : I→Finset (ℕ×ℕ)) : Finset (ℕ×ℕ):=
  Finset.univ.biUnion S

def uniformConstant {I : Type} [Fintype I] (K : I→ℝ) : ℝ:=1+∑i,max 0 (K i)

theorem degree_le_uniform {I : Type} [Fintype I] (d : I→ℕ) (i : I) :
    d i≤uniformDegree d := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)

theorem control_subset_uniform {I : Type} [Fintype I] (S : I→Finset (ℕ×ℕ)) (i : I) :
    S i⊆uniformControl S := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩

theorem uniformConstant_bounds {I : Type} [Fintype I] (K : I→ℝ) :
    1≤uniformConstant K ∧ ∀i,K i≤uniformConstant K := by
  have hs : (0:ℝ)≤∑i,max 0 (K i):=Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  refine ⟨by dsimp only [uniformConstant];linarith only [hs],?_⟩
  intro i
  have hi:=Finset.single_le_sum (s:=Finset.univ) (f:=fun i=>max 0 (K i))
    (fun _ _=>le_max_left _ _) (Finset.mem_univ i)
  have hk:=le_max_right (0:ℝ) (K i)
  dsimp only [uniformConstant]
  linarith only [hi,hk]

/-- Preserve each literal native source's own metadata and returned
family, while selecting the entire finite collection BEFORE Z. No
monotonicity callback or source-energy estimate is assumed here. Uniform
upper metadata are then available through the preceding three bounds. -/
theorem finite_original_subset_source_schedule
    {α : Type} [Fintype α]
    (Spec : Finset α→ℕ→Finset (ℕ×ℕ)→ℝ→ℝ→ℝ→Prop)
    (hsource : ∀J : Finset α,∃d : ℕ,∃S : Finset (ℕ×ℕ),
      ∃K : ℝ,0<K ∧ ∃C : ℝ,1≤C ∧ ∀ᶠ Z : ℝ in atTop,Spec J d S K C Z) :
    ∃(d : Finset α→ℕ)(S : Finset α→Finset (ℕ×ℕ))(K C : Finset α→ℝ),
      (∀J,0<K J) ∧ (∀J,1≤C J) ∧
      ∀ᶠ Z : ℝ in atTop,∀J : Finset α,Spec J (d J) (S J) (K J) (C J) Z := by
  classical
  choose d S K hK C hC hs using hsource
  exact ⟨d,S,K,C,hK,hC,Filter.eventually_all.2 hs⟩

/-- A threshold for the actual local source is uniform over every
rebased child base whose retained original unit is at least1/50. Never
specialize an eventual statement to a moving exponent without this step. -/
theorem eventually_all_rebased_sources (P : ℝ→Prop)
    (hP : ∀ᶠ Y : ℝ in atTop,P Y) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ)≤U→P (Z^U) := by
  obtain ⟨Y0,hY⟩:=Filter.eventually_atTop.1 hP
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/50)).eventually
    (eventually_ge_atTop Y0),eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro U hU
  exact hY _ (hz.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hU))

/-- A monotone physical source contract on every original subset gets
ONE common degree, profile control, terminal constant, deletion constant
and eventual threshold. The surviving subset is universally quantified
AFTER Z. The monotonicity is only enlargement of those scalar metadata;
the actual chosen source, deletion and returned family stay unchanged. -/
theorem finite_original_subset_source_uniformization
    {α : Type} [Fintype α]
    (Spec : Finset α→ℕ→Finset (ℕ×ℕ)→ℝ→ℝ→ℝ→Prop)
    (hmono : ∀(J : Finset α)(d d' : ℕ)(S S' : Finset (ℕ×ℕ))(K K' C C' Z : ℝ),
      d≤d'→S⊆S'→K≤K'→C≤C'→1≤K'→1≤C'→
      Spec J d S K C Z→Spec J d' S' K' C' Z)
    (hsource : ∀J : Finset α,∃d : ℕ,∃S : Finset (ℕ×ℕ),
      ∃K : ℝ,0<K ∧ ∃C : ℝ,1≤C ∧ ∀ᶠ Z : ℝ in atTop,Spec J d S K C Z) :
    ∃d : ℕ,∃S : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∃C : ℝ,1≤C ∧ ∀ᶠ Z : ℝ in atTop,∀J : Finset α,Spec J d S K C Z := by
  classical
  choose d S K hK C hC hs using hsource
  have hKs:=uniformConstant_bounds K
  have hCs:=uniformConstant_bounds C
  refine ⟨uniformDegree d,uniformControl S,uniformConstant K,by linarith only [hKs.1],
    uniformConstant C,hCs.1,?_⟩
  filter_upwards [Filter.eventually_all.2 hs] with Z hZ
  intro J
  exact hmono J _ _ _ _ _ _ _ _ Z (degree_le_uniform d J)
    (control_subset_uniform S J) (hKs.2 J) (hCs.2 J) hKs.1 hCs.1 (hZ J)

/-- Actual nonnegative source factors allow the detector constant to be
increased without changing the source coefficient or returned family. -/
theorem detector_factor_upgrade {C C' factor body : ℝ} {n : ℕ}
    (hC : 0≤C) (hCC : C≤C') (hf : 0≤factor) (hb : 0≤body) :
    C^n*factor*body≤C'^n*factor*body := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC hCC n) hf) hb

/-- The terminal factor has exactly the profile and height dependence of
NativeDaughterForest. This pays uniformizing its terminal metadata; no
source-energy estimate or count bound is a premise. -/
theorem terminal_factor_upgrade
    {K K' diagonal profile profile' height scale : ℝ} {d d' : ℕ}
    (hK : 0≤K) (hKK : K≤K') (hdiag : 0≤diagonal)
    (hp : 0≤profile) (hpp : profile≤profile') (hh : 1≤height)
    (hd : d≤d') (hs : 0≤ scale) :
    K*diagonal*profile^2*height^d*scale≤
      K'*diagonal*profile'^2*height^d'*scale := by
  have hK' : 0≤K':=hK.trans hKK
  have hp' : 0≤profile':=hp.trans hpp
  have hheight : 0≤height:=le_trans (by norm_num) hh
  have hprof : profile^2≤profile'^2:=pow_le_pow_left₀ hp hpp 2
  have hdeg : height^d≤height^d':=pow_le_pow_right₀ hh hd
  have h1:=mul_le_mul_of_nonneg_right hKK hdiag
  have h2:=mul_le_mul h1 hprof (sq_nonneg _) (mul_nonneg hK' hdiag)
  have h3:=mul_le_mul h2 hdeg (pow_nonneg hheight _) (by positivity : 0≤K'*diagonal*profile'^2)
  exact mul_le_mul_of_nonneg_right h3 hs

end
end OAI.SevenEighths.Cycle153SourceUniform
#print axioms OAI.SevenEighths.Cycle153SourceUniform.finite_original_subset_source_uniformization
#print axioms OAI.SevenEighths.Cycle153SourceUniform.detector_factor_upgrade
#print axioms OAI.SevenEighths.Cycle153SourceUniform.terminal_factor_upgrade

#print axioms OAI.SevenEighths.Cycle153SourceUniform.finite_original_subset_source_schedule

#print axioms OAI.SevenEighths.Cycle153SourceUniform.eventually_all_rebased_sources
