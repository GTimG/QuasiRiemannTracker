/- The genuine selected OLD source pays the final LOW target.
Copyright (c)2026 Zhongpai Gao. Native source by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.LowPhysical.ActualOldSelectedRows
import Candidate.Research.RecursiveAffine.NativeRawOldExponent
import Candidate.Research.RecursiveAffine.FiniteSourceUniformization

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass Cycle153RegionalLow
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice CenteredMomentFirstDiscardedEnergy
open Cycle63FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonAllocationSum CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentFirstExceptionalPrefactor Cycle153LowPhysical

/-- The actual OLD source bound, quantified over every ledger and moving
source after the common threshold. Original-subset and ledger choices do
not affect its fixed source constant. -/
def NativeSelectedOldPaidAt (budget : ℕ)(U r Kold Z : ℝ) : Prop :=
    2≤Z ∧ ∀(ledger : Cycle63.AffineLedger),
    letI : Cycle63.AffineLedger:=ledger
    ∀{alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
      (g : GeometryAffineLowSchedule)(hmu : g.μ=nativeMu)
      (reflected second : Bool)(s : Input alpha)(R : Ideal O)
      (Mrow amp xi reserve b firstHeight common sourcePad oldError omega mesh Kbox Cg fixed : ℝ)
      (Nrow : ℕ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
      (firstIndex : Label→GeometryLowFirstIndex reflected s R 1 (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)(Psi : 𝓢(ℝ,ℂ)),
    Fintype.card alpha≤ budget → 1≤ s.lower →
    (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
    sourceRadius s≤ Z^(3:ℝ) → 0≤ Cg → 0≤ fixed →
    (∀x,s.W₁ x≠0→(1/4)≤ x) → (∀x,s.W₂ x≠0→(1/4)≤ x) →
    (∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R 1 (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) R s.ν s.W s.P≠0) →
    Function.Injective (fun l=>(geometryFirstLabel s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,(firstIndex l).1.val.2.1.val)) →
    (∀l,sourceRadius (geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex l))≤ Z^(130:ℝ)) →
    common≤actualSourceCommon64 g (Fintype.card alpha) omega mesh →
    sourcePad≤g.μ/8 → 0≤Kbox →
    ∀box : Finset (Fin 4→ℤ),
    (∀r : NativeLowRows reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key hz1 hz2 firstIndex,
      actualSecondDyad
        (geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1))
        (R*geometryColumnIdeal reflected s R 1 (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)
        (firstIndex r.val.1).1.val.2.1.val
        (firstMainRadius reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve
          (geometryFirstLabel s R 1 (Z^Mrow) Z xi (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
            key (firstIndex r.val.1).1.val))
        (firstMainFourierScale reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve b
          Nrow (geometryFirstLabel s R 1 (Z^Mrow) Z xi
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)) Z xi r.val.2∈box) →
    (box.card:ℝ)≤Kbox*Z^r →
    Z^(Mrow+3*g.δ-amp+oldError)*Z^((1+9*((Fintype.card alpha:ℝ)+2))*r)*
      nativeOldSelectedCost reflected second s R Z Mrow amp xi reserve b firstHeight Nrow hZ key hz1 hz2
        firstIndex Psi g.δ r (common+sourcePad) Cg fixed ≤
      Kold*Cg*fixed*geometryHighFactor reflected 64 key*Kbox*
        Z^((Mrow+3*g.δ-amp+oldError)+geometryAffineLowTarget g (Fintype.card alpha) amp omega mesh+(1-Mrow))

/-- Invoke the genuine native selected OLD source before choosing the
moving base, rounded ledger, source or surviving original subset. The
actual box count and physical residual surcharge are explicitly paid. -/
theorem eventual_actual_selected_old_rows_paid
    {Bnorm : ℝ}(hB : 0≤Bnorm)(budget : ℕ)(U : ℝ)(hU : 0≤U) :
    let r:=postDictionaryRate Bnorm budget
    ∃Kold : ℝ,0<Kold ∧ ∀ᶠ Z : ℝ in atTop,NativeSelectedOldPaidAt budget U r Kold Z := by
  intro r
  have hr : 0<r:=(postDictionaryRate_budgets hB budget).1
  obtain ⟨Kold,hKold,hs⟩:=eventual_actual_selected_old_rows budget 1 (1/4) r 130 r U r
    (by norm_num) (by norm_num) hr (by norm_num) hr hU hr
  refine ⟨Kold,hKold,?_⟩
  filter_upwards [hs] with Z hsource
  refine ⟨hsource.1,?_⟩
  intro ledger
  letI : Cycle63.AffineLedger:=ledger
  intro alpha Label _ _ _ g hmu reflected second s R Mrow amp xi reserve b firstHeight
    common sourcePad oldError omega mesh Kbox Cg fixed Nrow hZ key hz1 hz2 firstIndex Psi
    hN hlower hpool hsourceRadius hCg hfixed hs1 hs2 hf hinj hchild hcommon hpad hKbox box hbox hboxcard
  have hold:=hsource.2 reflected second s R Mrow amp xi reserve b firstHeight 3 g.δ r
    (common+sourcePad) Cg fixed Nrow hZ key hz1 hz2 firstIndex Psi hN hlower hpool hsourceRadius
    (by norm_num) g.δ_pos.le hr.le hCg hfixed hs1 hs2 hf hinj hchild box hbox
  have hphysical : 0≤geometryHighFactor reflected 64 key :=
    (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have hsupport : geometrySupportConstant budget 1 (1/4) (1/4)=(64:ℝ) :=by
    norm_num [geometrySupportConstant]
  rw [hsupport] at hold
  let A:=Kold*Cg*fixed*geometryHighFactor reflected 64 key
  have hA : 0≤A:=mul_nonneg (mul_nonneg (mul_nonneg hKold.le hCg) hfixed) hphysical
  let outer:=Mrow+3*g.δ-amp+oldError
  let extra:=(1+9*((Fintype.card alpha:ℝ)+2))*r
  let E:=3*g.δ+amp+(common+sourcePad)+(1-Mrow)+r+130*r+r+r
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  have hpaid:=native_raw_old_exponent_le_target g hmu hB budget (Fintype.card alpha) hN
    amp omega mesh Mrow oldError common sourcePad hcommon hpad
  dsimp only at hpaid
  change Z^outer*Z^extra*nativeOldSelectedCost reflected second s R Z Mrow amp xi reserve b firstHeight
    Nrow hZ key hz1 hz2 firstIndex Psi g.δ r (common+sourcePad) Cg fixed≤_
  change nativeOldSelectedCost reflected second s R Z Mrow amp xi reserve b firstHeight
    Nrow hZ key hz1 hz2 firstIndex Psi g.δ r (common+sourcePad) Cg fixed≤A*(box.card:ℝ)*Z^E at hold
  calc
    _≤Z^outer*Z^extra*(A*(box.card:ℝ)*Z^E) :=
      mul_le_mul_of_nonneg_left hold (mul_nonneg (Real.rpow_nonneg hZ0.le _) (Real.rpow_nonneg hZ0.le _))
    _≤Z^outer*Z^extra*(A*(Kbox*Z^r)*Z^E) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hboxcard hA) (Real.rpow_nonneg hZ0.le _))
        (mul_nonneg (Real.rpow_nonneg hZ0.le _) (Real.rpow_nonneg hZ0.le _))
    _=A*Kbox*Z^(1+3*g.δ+oldError+3*g.δ+common+sourcePad+
        135*r+9*((Fintype.card alpha:ℝ)+2)*r) :=by
      calc
        _=A*Kbox*(Z^outer*Z^extra*Z^r*Z^E) :=by ring
        _=A*Kbox*Z^(((outer+extra)+r)+E) :=by
          rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
        _=_ :=by congr 2;dsimp only[outer,extra,E];ring
    _≤A*Kbox*Z^((Mrow+3*g.δ-amp+oldError)+
        geometryAffineLowTarget g (Fintype.card alpha) amp omega mesh+(1-Mrow)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hpaid) (mul_nonneg hA hKbox)


/-- One genuine OLD threshold covers every actual rebased node and all
rounded ledgers; the retained unit is the real native lower bound1/50. -/
theorem eventual_actual_selected_old_rows_paid_rebased
    {Bnorm : ℝ}(hB : 0≤Bnorm)(budget : ℕ)(U : ℝ)(hU : 0≤U) :
    let r:=postDictionaryRate Bnorm budget
    ∃Kold : ℝ,0<Kold ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀unit : ℝ,(1/50:ℝ)≤unit→NativeSelectedOldPaidAt budget U r Kold (Z^unit) :=by
  obtain ⟨Kold,hKold,hs⟩:=eventual_actual_selected_old_rows_paid hB budget U hU
  exact ⟨Kold,hKold,Cycle153SourceUniform.eventually_all_rebased_sources _ hs⟩

end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.eventual_actual_selected_old_rows_paid

#print axioms OAI.SevenEighths.Cycle153SourceSchedule.eventual_actual_selected_old_rows_paid_rebased
