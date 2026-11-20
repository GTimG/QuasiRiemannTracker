/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Honest native short-inverse count on the original same-zero flagged rows.
The enhanced E(19)/E(25) curve is a separate, stronger source obligation. -/
import Candidate.C092.transport.MediumInversePriceActual

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

/-- The native prime-amplified inverse source supplies the literal deficit
ν*r0+2*q*z on every further subset of the original B fiber. Its original
untapered and conductor caps are explicit and have not been enlarged. -/
theorem original_native_short_inverse_count (D : Cycle25.Weighted.MomentData)
    (S : WeightedSourceData D) :
    ∃ J : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a ε cutoff T allowance i),
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.upper=(fun _ => 2) →
    B.widths=(fun s => D.ell s/d) → (∀ s, (B.external s).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height z r0 : ℝ, 0 ≤ height → 1/2 ≤ a →
    2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne
    0 ≤ z → z ≤ 7/37 → F.r+2*z < 1 → 2*F.r+8*z < 3 → r0 ≤ F.r →
    ∀ rows : Finset FreeRow, rows ⊆ F.rows →
    (rows.card : ℝ) ≤ (12*(1+height)*(C*(1+height)^J))*
      (Z^d)^(1-((2*a-1)*r0+2*F.q*z)+2*ε+(2*a-1)*F.mesh+D.t) := by
  obtain ⟨J,hcount⟩ := QRH.Cycle092.DirectCount.source_marked_inverse_fiber_count D S
  refine ⟨J,?_⟩
  intro η
  obtain ⟨C,hC,hcount⟩ := hcount η
  refine ⟨C,hC,hcount.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro d hd a ε cutoff T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height z r0 hh ha hf
  dsimp only
  intro hz0 hzmax hcap1 hcap2 hr0 rows hrows
  have hU : 1 < Z^d := Real.one_lt_rpow hz.1 (by linarith)
  have hc := hz.2 d hd a ε cutoff T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height z hh ha hf hz0 hzmax hcap1 hcap2
  apply (Nat.cast_le.mpr (Finset.card_le_card hrows)).trans (hc.trans ?_)
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hU.le
  have h := mul_le_mul_of_nonneg_left hr0 (show 0 ≤ 2*a-1 by linarith)
  linarith

/-- One inward-rounded repeat count loses less than one actual descriptor
width. A positive fixed minimum width also gives an early finite count bank. -/
theorem repeat_count_rounding {P Pmax w wmin : ℝ}
    (hP : 0 ≤ P) (hPmax : P ≤ Pmax) (hw : 0 < wmin) (hwm : wmin ≤ w) :
    ∃ k : ℕ, k ≤ ⌊Pmax/wmin⌋₊ ∧
      (k : ℝ)*w ≤ P ∧ P-w < (k : ℝ)*w := by
  have hwp : 0 < w := hw.trans_le hwm
  refine ⟨⌊P/w⌋₊,?_,?_,?_⟩
  · apply Nat.floor_mono
    exact (div_le_div_of_nonneg_left hP hw hwm).trans
      (div_le_div_of_nonneg_right hPmax hw.le)
  · exact (le_div_iff₀ hwp).mp (Nat.floor_le (div_nonneg hP hwp.le))
  · have h := (div_lt_iff₀ hwp).mp (Nat.lt_floor_add_one (P/w))
    nlinarith

#print axioms original_native_short_inverse_count
#print axioms repeat_count_rounding
end
end QRH.Cycle092.MediumInversePrice
