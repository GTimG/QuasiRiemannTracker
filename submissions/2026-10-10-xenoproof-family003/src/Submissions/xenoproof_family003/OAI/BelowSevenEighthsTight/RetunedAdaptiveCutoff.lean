import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedRowCountBranches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness

/- The adaptive cutoff is retuned for any admissible comparison capacity.
   The witness theorem uses the original detector with the new cutoff; it
   neither changes the underlying characters nor asserts moment estimates. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.FiberExtension
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths
open HeckeFamily HeckeDetectorSupportedWitness RowCountExtension

def cutoff (κ₀ δ q : ℝ) : ℝ :=
  if δ≤5/6 then adaptiveSplit (1/(3*κ₀)) δ (1/2-min (1/2) (max 0 (q/δ))) else 3/2

theorem cutoff_bounds (κ₀ δ q : ℝ) (hk₀ : 13/18≤κ₀) (hk₀u : κ₀≤3/4)
    (hδ : 0≤δ) : 1≤cutoff κ₀ δ q ∧ cutoff κ₀ δ q≤3/2 := by
  have hc := reciprocal_range κ₀ hk₀ hk₀u
  unfold cutoff
  split_ifs with hd
  · apply adaptive_split_range _ _ _ hc.1 hc.2 hδ hd
    · linarith [min_le_left (1/2:ℝ) (max 0 (q/δ))]
    · have hx : 0≤min (1/2:ℝ) (max 0 (q/δ)) :=
        le_min (by norm_num) (le_max_left _ _)
      linarith
  · norm_num

theorem cutoff_eq_balanced (κ₀ δ q : ℝ) (hδ : 0<δ) (hd : δ≤5/6)
    (hq : 0≤q) (hq' : q≤δ/2) :
    cutoff κ₀ δ q=adaptiveSplit (1/(3*κ₀)) δ (1/2-q/δ) := by
  have hx : 0≤q/δ := div_nonneg hq hδ.le
  have hx' : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoff,ite_eq_left hd,max_eq_right hx,min_eq_right hx']

theorem cutoff_eq_high (κ₀ δ q : ℝ) (hδ : 5/6<δ) : cutoff κ₀ δ q=3/2 := by
  simp only [cutoff,ite_eq_right (not_le_of_gt hδ)]

theorem balanced_count_identity (κ₀ δ x : ℝ)
    (hk₀ : 13/18≤κ₀) (hk₀u : κ₀≤3/4) (hδ : 0≤δ) (hδu : δ≤5/6)
    (hx : 0≤x) (hxu : x≤1/2) :
    max (shortExponent (1/(3*κ₀)) δ x (adaptiveSplit (1/(3*κ₀)) δ (1/2-x)))
      (longExponent δ (adaptiveSplit (1/(3*κ₀)) δ (1/2-x))) =
      rowEnvelope (1/(3*κ₀)) δ (1/2-x) := by
  have hc := reciprocal_range κ₀ hk₀ hk₀u
  have hy : 0≤1/2-x := by linarith
  have hyu : 1/2-x≤1/2 := by linarith
  have hD := denominator_lower hc.1 hc.2 hx hxu
  have hJ := generalized_J_lower (1/(3*κ₀)) δ (1/2-x) hc.1 hc.2 hδ hδu hy hyu
  have hD' : 5/2-1/(3*κ₀)+(1+2*(1/(3*κ₀)))*(1/2-x)≠0 := by
    have he := (source_coordinate_identities (1/(3*κ₀)) (1/2-x)).1
    have hxid : (1/2:ℝ)-(1/2-x)=x := by ring
    rw [hxid] at he
    rw [←he]
    linarith
  have hs := short_at_adaptive_split (1/(3*κ₀)) δ (1/2-x) hD'
    (by unfold commonDenominator; linarith)
  have hxid : (1/2:ℝ)-(1/2-x)=x := by ring
  rw [hxid] at hs
  rw [hs, longExponent, long_at_adaptive_split, max_self]

theorem actual_adaptive_witnesses (κ₀ dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hk₀ : 13/18≤κ₀) (hk₀u : κ₀≤3/4)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) → ∀ q : Row→ℝ,
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε (cutoff κ₀ (2*a-1) (q u))
            (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ q
  have hδ : 0≤2*a-1 := by linarith
  exact ⟨fun u => (Classical.choice (hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha'
    hnext hcurrent hQ (cutoff κ₀ (2*a-1) (q u))
      (cutoff_bounds κ₀ (2*a-1) (q u) hk₀ hk₀u hδ).1
      (cutoff_bounds κ₀ (2*a-1) (q u) hk₀ hk₀u hδ).2)) u⟩

#print axioms balanced_count_identity
#print axioms actual_adaptive_witnesses
end
end BelowSevenEighthsTight.FiberExtension
