/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeoSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Provider

/-! A direct native source, including zero marked width. The artificial negative-cap
parent has no admissible inputs; it is used only to reuse the generic source step. -/
namespace Qrh.JointDetector.NativeDirectSource
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open QRH.SilDensitySplit.CubeFree

/-- A negative cap excludes every input in the literal unit-source contract. -/
theorem negative_cap_source (B L c : ℝ) (hc : c < 0) : GlobalSource B L c := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨0, ∅, 1, by norm_num, Filter.Eventually.of_forall ?_⟩
  intro Z T θ w σ v t height hw hwm hlo hhi hh hv M hM hM' Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm
  have h := hadm.2.2.2.2.2.1
  change (∑ i, w i) ≤ c * M at h
  have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  have hm : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have : c * M < 0 := mul_neg_of_neg_of_pos hc hm
  linarith

def data (B : ℝ) : StepData where
  B₀ := B
  L₀ := 5
  c₀ := -1
  B := B
  L := 4
  c := 1/10
  κ := 3/4
  s₀ := 0
  Hmin := 7/10
  Hmax := 3
  sel := fun _ w => 11/25*w
  price := nativePrice (3/4) (by norm_num)

theorem gates (B : ℝ) (hB : B < 1) : StepGates (data B) where
  face := by simp only [data]; exact ⟨le_rfl, hB, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  kappa := rfl
  crossing := by simp [data]
  envelope := by norm_num [data]
  sel_spec := by
    intro ε hε
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      change 11/25*x ≤ 11/25*y
      linarith
    · intro w hw hwc
      change 0 ≤ 11/25*w ∧ 11/25*w ≤ w
      constructor <;> linarith
  ledger := by
    intro ε hε
    refine ⟨(ε/16, 1/1000, 1/100), ?_⟩
    refine ⟨by positivity, ?_, by norm_num, by norm_num, ?_⟩
    · change ε/16 ≤ ε/(16*(3/4))
      linarith
    intro mesh hm hm' tl ht ht' g hfloor
    have hsel := g.hsel
    have hs := g.hs
    have hS := g.hS
    have hf := g.hf
    have hgt := g.ht
    change 11/25*(g.S-g.f) ≤ g.u ∧ g.u ≤ 11/25*(g.S-g.f)+mesh at hsel
    change 0 ≤ g.S ∧ g.S ≤ 1/10 at hS
    have hu : 0 ≤ g.u := by
      have := hs.2
      linarith
    have huc : g.u ≤ 11/250 + mesh := by linarith
    refine ⟨?_, ?_, ?_⟩
    · change 7/10 ≤ 1+g.t-6*g.u
      linarith
    · change 1+g.t-6*g.u ≤ 3
      linarith
    · change 3/4 * max 0 g.s ≤ g.u+ε/16
      rw [max_eq_right hs.1]
      linarith
  reference := by
    refine ⟨min (1-B) (1/750), lt_min (by linarith) (by norm_num), ?_⟩
    intro ε hε S hS hSc
    have h1 := min_le_left (1-B) (1/750:ℝ)
    have h2 := min_le_right (1-B) (1/750:ℝ)
    change 0 ≤ S at hS
    change S ≤ 1/10 at hSc
    simp only [data]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

/-- The native packed estimate supplies a source arbitrarily close to intercept one.
No positive-cap parent source is assumed. -/
theorem global_source (B : ℝ) (hB : B < 1)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : GlobalSource B 4 (1/10) := by
  let D := data B
  let G := gates B hB
  have hleaf : PricedPackedSource D.price D.Hmin (D.Hmax+1) 4 := by
    exact native_priced_source hβ _ _ _ (by norm_num [D, data])
      (by norm_num [D, data])
  have I : StepInputs D G 4 := Assembly.step_inputs_of_provider D G 4
    (fun _ hl => Second.Provider.contrary_raw_side_provider G 4 (by norm_num) hl
      (Second.ProviderDiag.diag_supply G))
  exact cubefree_step D G 4 I hβ (negative_cap_source B 5 (-1) (by norm_num)) hleaf

end
end Qrh.JointDetector.NativeDirectSource

#print axioms Qrh.JointDetector.NativeDirectSource.global_source
