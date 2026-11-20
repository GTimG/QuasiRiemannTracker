/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual amplified inverse count on the original same-zero Batch fiber. -/
import Candidate.C092.transport.DirectCountInverse
import Candidate.C092.transport.DirectCountMarkedInverse
import Candidate.C092.transport.MediumWitnessSharedBatch

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

def longDeficit (ν cutoff : ℝ) : ℝ := 5/6-(5/6-ν)*cutoff

theorem amplified_exponent {ν r cutoff ε : ℝ}
    (hν : 0 ≤ ν) (hνhi : ν ≤ 5/6) (hr : 1 ≤ r)
    (hcap : r ≤ cutoff+ε) (hε : 0 ≤ ε) :
    sourceExponent r-ν*r+2*ε ≤ 1-longDeficit ν cutoff+3*ε := by
  rw [sourceExponent,max_eq_right (by linarith only [hr])]
  have h := mul_le_mul_of_nonneg_left hcap (sub_nonneg.mpr hνhi)
  dsimp [longDeficit]
  nlinarith

/-- The count comes from genuine inverse amplification. Restricting the
fiber to additional actual inverse/mark flags preserves the identical
attaining zero and both dyadic lengths; no fresh witness is selected. -/
theorem original_long_inverse_count (D : Cycle25.Weighted.MomentData)
    (S : WeightedSourceData D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ J : ℕ, ∀ η : Character,
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a ε cutoff T allowance i),
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.upper=(fun _ => 2) →
    B.widths=(fun s => D.ell s/d) → (∀ s, (B.external s).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height : ℝ, 0 ≤ height → 1/2 ≤ a → 2*a-1 ≤ 5/6 → 0 ≤ ε →
    2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne
    1 ≤ F.r → F.r ≤ 2 →
    ∀ rows : Finset FreeRow, rows ⊆ F.rows →
    (rows.card : ℝ) ≤ (12*(1+height)*((C*(1+height)^J)*K))*
      (Z^d)^(1-longDeficit (2*a-1) cutoff+3*ε+D.t) := by
  obtain ⟨K,hK,J,hcount⟩ := QRH.Cycle092.DirectCount.source_inverse_fiber_count D S
  refine ⟨K,hK,J,?_⟩
  intro η
  obtain ⟨C,hC,hcount⟩ := hcount η
  refine ⟨C,hC,hcount.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro d hd a ε cutoff T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height hh ha hνhi hε hf
  dsimp only
  intro hr hrhi rows hrows
  let F := B.fiber bin label left right hne
  have hZp : 0 < Z := zero_lt_one.trans hz.1
  have hU : 1 < Z^d := Real.one_lt_rpow hz.1 (by linarith)
  obtain ⟨u,hu⟩ := F.nonempty
  have hsame : (F.witness u).r=F.r := by
    rw [(F.witness u).toWitness.left_exponent hU,F.fixed_left u hu]
    rfl
  have hcap : F.r ≤ cutoff+ε := by
    rw [←hsame]
    exact (F.witness u).inverse_length_upper
  have he := amplified_exponent (by linarith : 0 ≤ 2*a-1) hνhi hr hcap hε
  have hc := hz.2 d hd a ε cutoff T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height hh ha hf (by linarith) hrhi
  apply (Nat.cast_le.mpr (Finset.card_le_card hrows)).trans (hc.trans ?_)
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hU.le
  linarith

#print axioms original_long_inverse_count
end
end QRH.Cycle092.MediumInversePrice
