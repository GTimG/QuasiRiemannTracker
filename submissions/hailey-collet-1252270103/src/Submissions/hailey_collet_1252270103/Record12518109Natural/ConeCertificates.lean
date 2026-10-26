/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.ConeCore
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Record12518109Natural.Valuation
noncomputable section
open scoped Classical BigOperators
open CenteredMomentActive Record12518109Natural.FirstNumeratorValuation

def cone0_0_0 : Fin 6 → ℝ := ![25/38,1/2,-1,3/4,-1/4,-1]
theorem cone0_0_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_0_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_0_0,point,sourceExponent,netExponent]
theorem cone0_0_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_0_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_0_0
    (by norm_num [cone0_0_0]) (by norm_num [cone0_0_0]) cone0_0_0_residues

def cone0_0_1 : Fin 6 → ℝ := ![22/19,1/5,-1,17/20,-1/4,-1]
theorem cone0_0_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_0_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_0_1,point,sourceExponent,netExponent]
theorem cone0_0_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_0_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_0_1
    (by norm_num [cone0_0_1]) (by norm_num [cone0_0_1]) cone0_0_1_residues

def cone0_1_0 : Fin 6 → ℝ := ![11/76,65/76,-1,51/76,-1/4,-1]
theorem cone0_1_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_1_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_1_0,point,sourceExponent,netExponent]
theorem cone0_1_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_1_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_1_0
    (by norm_num [cone0_1_0]) (by norm_num [cone0_1_0]) cone0_1_0_residues

def cone0_1_1 : Fin 6 → ℝ := ![11/76,65/76,-1,51/76,-1/4,-1]
theorem cone0_1_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone0_1_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone0_1_1,point,sourceExponent,netExponent]
theorem cone0_1_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone0_1_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone0_1_1
    (by norm_num [cone0_1_1]) (by norm_num [cone0_1_1]) cone0_1_1_residues

theorem common_endpoint0 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (1/4) (weighted s i j w) ≤ (3/19)*weighted s i j w 0 := by
  let x := weighted s i j w
  change commonValue (1/4) x ≤ (3/19)*x 0
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  by_cases hc : x 1 ≤ x 0
  · have hm : 0 ≤ x 0-x 1 := by linarith
    have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · have hr := cone0_1_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_1_1 x at hr
      simp only [commonValue,surplus,max_eq_left hm,max_eq_left hb,max_eq_right hn]
      norm_num [linear,cone0_1_1] at hr
      linarith
    · have hr := cone0_1_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_1_0 x at hr
      have hb0 : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_left hm,max_eq_right hb0,max_eq_right hn]
      norm_num [linear,cone0_1_0] at hr
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cone0_0_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_0_1 x at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      norm_num [linear,cone0_0_1] at hr
      linarith
    · have hr := cone0_0_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone0_0_0 x at hr
      have hb0 : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_right hb0]
      norm_num [linear,cone0_0_0] at hr
      linarith

def cone1_0_0 : Fin 6 → ℝ := ![25/38,1/2,-1,259/304,-107/304,-1]
theorem cone1_0_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_0_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_0_0,point,sourceExponent,netExponent]
theorem cone1_0_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_0_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_0_0
    (by norm_num [cone1_0_0]) (by norm_num [cone1_0_0]) cone1_0_0_residues

def cone1_0_1 : Fin 6 → ℝ := ![245/228,1/4,-1,853/912,-107/304,-1]
theorem cone1_0_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_0_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_0_1,point,sourceExponent,netExponent]
theorem cone1_0_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_0_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_0_1
    (by norm_num [cone1_0_1]) (by norm_num [cone1_0_1]) cone1_0_1_residues

def cone1_1_0 : Fin 6 → ℝ := ![75/304,229/304,-1,235/304,-107/304,-1]
theorem cone1_1_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_1_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_1_0,point,sourceExponent,netExponent]
theorem cone1_1_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_1_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_1_0
    (by norm_num [cone1_1_0]) (by norm_num [cone1_1_0]) cone1_1_0_residues

def cone1_1_1 : Fin 6 → ℝ := ![75/304,229/304,-1,235/304,-107/304,-1]
theorem cone1_1_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone1_1_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone1_1_1,point,sourceExponent,netExponent]
theorem cone1_1_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone1_1_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone1_1_1
    (by norm_num [cone1_1_1]) (by norm_num [cone1_1_1]) cone1_1_1_residues

theorem common_endpoint1 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (107/304) (weighted s i j w) ≤ (3/19)*weighted s i j w 0 := by
  let x := weighted s i j w
  change commonValue (107/304) x ≤ (3/19)*x 0
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  by_cases hc : x 1 ≤ x 0
  · have hm : 0 ≤ x 0-x 1 := by linarith
    have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · have hr := cone1_1_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_1_1 x at hr
      simp only [commonValue,surplus,max_eq_left hm,max_eq_left hb,max_eq_right hn]
      norm_num [linear,cone1_1_1] at hr
      linarith
    · have hr := cone1_1_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_1_0 x at hr
      have hb0 : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_left hm,max_eq_right hb0,max_eq_right hn]
      norm_num [linear,cone1_1_0] at hr
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cone1_0_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_0_1 x at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      norm_num [linear,cone1_0_1] at hr
      linarith
    · have hr := cone1_0_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone1_0_0 x at hr
      have hb0 : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_right hb0]
      norm_num [linear,cone1_0_0] at hr
      linarith

def cone2_0_0 : Fin 6 → ℝ := ![1481/1900,326/475,-1,853/950,-23/50,-1]
theorem cone2_0_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_0_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_0_0,point,sourceExponent,netExponent]
theorem cone2_0_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_0_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_0_0
    (by norm_num [cone2_0_0]) (by norm_num [cone2_0_0]) cone2_0_0_residues

def cone2_0_1 : Fin 6 → ℝ := ![113/75,1/4,-1,313/300,-23/50,-1]
theorem cone2_0_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_0_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_0_1,point,sourceExponent,netExponent]
theorem cone2_0_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_0_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_0_1
    (by norm_num [cone2_0_1]) (by norm_num [cone2_0_1]) cone2_0_1_residues

def cone2_1_0 : Fin 6 → ℝ := ![563/740,637/925,-1,823/925,-23/50,-1]
theorem cone2_1_0_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_1_0 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_1_0,point,sourceExponent,netExponent]
theorem cone2_1_0_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_1_0 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_1_0
    (by norm_num [cone2_1_0]) (by norm_num [cone2_1_0]) cone2_1_0_residues

def cone2_1_1 : Fin 6 → ℝ := ![563/740,637/925,-1,823/925,-23/50,-1]
theorem cone2_1_1_residues (i j : ℕ) (hi : 1 ≤ i) (hi6 : i ≤ 6)
    (hj : 1 ≤ j) (hj6 : j ≤ 6) : 0 ≤ linear cone2_1_1 (point i j) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [linear,cone2_1_1,point,sourceExponent,netExponent]
theorem cone2_1_1_nonnegative {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    0 ≤ linear cone2_1_1 (weighted s i j w) := by
  exact weighted_linear_nonnegative s i j w hw hi hj cone2_1_1
    (by norm_num [cone2_1_1]) (by norm_num [cone2_1_1]) cone2_1_1_residues

theorem common_endpoint2 {ι : Type*} (s : Finset ι) (i j : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ t∈s,0 ≤ w t) (hi : ∀ t∈s,0 < i t) (hj : ∀ t∈s,0 < j t) :
    commonValue (23/50) (weighted s i j w) ≤ (59/100)*weighted s i j w 0 := by
  let x := weighted s i j w
  change commonValue (23/50) x ≤ (59/100)*x 0
  have h0 : 0 ≤ x 0 := weighted_nonnegative s i j w hw 0
  have h1 : 0 ≤ x 1 := weighted_nonnegative s i j w hw 1
  have h3 : 0 ≤ x 3 := weighted_nonnegative s i j w hw 3
  by_cases hc : x 1 ≤ x 0
  · have hm : 0 ≤ x 0-x 1 := by linarith
    have hn : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 0-5*x 1-x 3
    · have hr := cone2_1_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_1_1 x at hr
      simp only [commonValue,surplus,max_eq_left hm,max_eq_left hb,max_eq_right hn]
      norm_num [linear,cone2_1_1] at hr
      linarith
    · have hr := cone2_1_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_1_0 x at hr
      have hb0 : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_left hm,max_eq_right hb0,max_eq_right hn]
      norm_num [linear,cone2_1_0] at hr
      linarith
  · have hm : x 0-x 1 ≤ 0 := by linarith
    have hn : 3*x 0-5*x 1-x 3 ≤ 0 := by linarith
    by_cases hb : 0 ≤ 3*x 1-5*x 0-x 3
    · have hr := cone2_0_1_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_0_1 x at hr
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_left hb]
      norm_num [linear,cone2_0_1] at hr
      linarith
    · have hr := cone2_0_0_nonnegative s i j w hw hi hj
      change 0 ≤ linear cone2_0_0 x at hr
      have hb0 : 3*x 1-5*x 0-x 3 ≤ 0 := by linarith
      simp only [commonValue,surplus,max_eq_right hm,max_eq_right hn,max_eq_right hb0]
      norm_num [linear,cone2_0_0] at hr
      linarith

end
end OAI.SevenEighths.Record12518109Natural.Valuation
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.common_endpoint0
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.common_endpoint1
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.common_endpoint2
