/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.BufferedCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatchSubset

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorClassBudget
local notation "O" => HeckeFamily.O

/-- Actual buffered zeros supply the witnesses in the rooted source count.
The card-bound callback is applied only to literal row restrictions of N;
no witness, rowwise coefficient choice or moment is added to N's data. -/
theorem actual_buffered_rooted_count
    (dmin dmax τ ε e κ η : ℝ) (n : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃Z₀ : ℝ,∀Z : ℝ,Z₀≤Z → ∀d : ℝ,dmin≤d → d≤dmax →
    ∀{Label Slot : Type}[Fintype Label]
      {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
      {hH : RayOrthogonality.globalUnits M≤H}
      {base anchor : Label→Character}{bad : Label→Ideal O}{W : ℝ→ℂ}{Aroot : ℝ},
    ∀N : RootedBatch (Slot:=Slot) M H hH base anchor bad W (Z^d) Aroot,
    ∀(a₀ tstar K : ℝ),1<Z^d → 2<Z^τ → 0<n → (49/100:ℝ)≤(n:ℝ)*e →
      51/100<a₀ → 1≤tstar → tstar≤3/2 → 0≤K →
    ∀hχ : ∀u : N.rows,∀j,(N.family u.val j).residue≠1,
    (∀u : N.rows,∀j,(N.family u.val j).modulus.absNorm≤Z^d) →
    (∀u : N.rows,a₀+e≤HeckeDetectorZeros.zeroMaximum (N.family u.val) (hχ u) (Z^τ)) →
    (∀F : Finset FreeRow,F⊆N.rows → ∀i : ℕ,i≤n →
      ∀χ : FreeRow→Label→Character,(∀u∈F,χ u=N.family u) →
      (∀u,SupportedWitness (χ u) (Z^d) a₀ ε tstar (Z^τ)
        ((Z^d)^(τ/(2*dmax))) i) → (F.card:ℝ)≤K) →
    (N.rows.card:ℝ)≤((n+1:ℕ):ℝ)*(⌈1/e⌉₊+2:ℕ)*K := by
  obtain ⟨Z₀,hconstruct⟩ := actual_supported_free_family dmin dmax τ ε e κ η n
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Label Slot _ M _ H hH base anchor bad W Aroot N a₀ tstar K
    hU hT hn hwidth ha₀ ht ht' hK hχ hconductor hzero hcount
  apply count_of_buffered_witnesses N.rows N.family hχ (Z^d) a₀ ε (Z^τ)
    ((Z^d)^(τ/(2*dmax))) e tstar K n hU hT he hn hwidth ha₀ hK hzero ?_ hcount
  intro F hF hne a i hi haa₀ ha hcurrent hnext
  let family : F→Label→Character := fun u=>N.family u.val
  have hχF : ∀u j,(family u j).residue≠1 := fun u j=>hχ ⟨u.val,hF u.property⟩ j
  obtain ⟨χ,hχ',⟨w⟩⟩ := hconstruct Z hZ d hd hd' F hne family hχF a i hi
    (ha₀.trans_le haa₀) ha hnext hcurrent
    (fun u j=>hconductor ⟨u.val,hF u.property⟩ j) tstar ht ht'
  refine ⟨χ,?_,⟨w⟩⟩
  intro u hu
  exact hχ' ⟨u,hu⟩

end
end Qrh.JointDetector.RepeatedMarks
