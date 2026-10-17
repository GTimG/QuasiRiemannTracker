import Candidate.Target830.High.Coordinates
import Candidate.Target830.Marked.Schedule
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowRows

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Cycle63InitialMass
open Target830 Marked830Plain
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSourceRow
open Cycle63FinalNatural CenteredMomentEnergyState Cycle63Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open LocalMoment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainHighRowsSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The inclusive high cut keeps both literal buffered height intervals.
No zero, character, puncture or row is replaced by an abstract datum. -/
theorem actual_main_high_bin_intervals
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hhigh : 81/100 ≤ bufferValue e p) :
    81/100 ≤ bufferValue e p ∧ bufferValue e p ≤ 7/8 ∧
      bufferValue e p ≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T)<bufferValue e p+e ∧
      bufferValue e p ≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T)<bufferValue e p+2*e := by
  obtain ⟨_,_,_,hb,hcl,hcu,hnl,hnu,_⟩ := hbin
  exact ⟨hhigh,hb,hcl,hcu,hnl,hnu⟩

/-- The complete signed ordinary row set has actual buffered bins. The
high source filter can use this one selector on each fixed physical ray pair;
the same keep witness is retained in all zero-maximum gates. -/
theorem actual_main_high_buffered_rows
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    ∃keep : ∀z : rows,st.radial.keep z.val,
    ∃select : rows→BufferIndex e,∀z : rows,
      1 ≤ (st.radial.profile (normValue z.val/st.radial.scale)).re ∧
      st.radial.profile (normValue z.val/st.radial.scale)≠0 ∧ z.val≠0 ∧
      GeometryZeroBin M H hH st η₀ hQM hQη z.val (keep z) e T (select z) ∧
      (81/100 ≤ bufferValue e (select z) →
        81/100 ≤ bufferValue e (select z) ∧ bufferValue e (select z) ≤ 7/8 ∧
        bufferValue e (select z) ≤ geometryRowMaximum M H hH st η₀ hQM hQη
          z.val (keep z) ((3*(select z).1.val:ℕ)*T) ∧
        geometryRowMaximum M H hH st η₀ hQM hQη z.val (keep z)
          ((3*(select z).1.val:ℕ)*T)<bufferValue e (select z)+e ∧
        bufferValue e (select z) ≤ geometryRowMaximum M H hH st η₀ hQM hQη
          z.val (keep z) (3*((select z).1.val+1:ℕ)*T) ∧
        geometryRowMaximum M H hH st η₀ hQM hQη z.val (keep z)
          (3*((select z).1.val+1:ℕ)*T)<bufferValue e (select z)+2*e) := by
  intro st rows
  have ha (z : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) z.val z.property
  let keep : ∀z : rows,st.radial.keep z.val := fun z=>(ha z).1
  have hp (z : rows) := actual_geometry_zero_partition M H hH st η₀ hQM hQη
    z.val (keep z) e T he hT hβlo hβhi
  let select : rows→BufferIndex e := fun z=>Classical.choose (hp z)
  refine ⟨keep,select,?_⟩
  intro z
  have hs : st.radial.profile (normValue z.val/st.radial.scale)≠0 := by
    intro hzero
    have hb := (ha z).2.2
    rw [hzero] at hb
    norm_num at hb
  have hbin := Classical.choose_spec (hp z)
  exact ⟨(ha z).2.2,hs,st.row_ne_zero z.val (keep z),hbin,
    actual_main_high_bin_intervals M H hH st η₀ hQM hQη z.val (keep z) e T (select z) hbin⟩

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_main_high_bin_intervals
#print axioms OAI.SevenEighths.TargetHigh830.actual_main_high_buffered_rows
