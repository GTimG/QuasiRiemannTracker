/- Fixed pre-source native OLD and absolute-box thresholds. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedOldTarget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineLowPayment

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open Filter Cycle63InitialMass Cycle153SourceSchedule

/-- Genuine native OLD constant, chosen before any moving source/ledger. -/
def actualSelectedOldConstant (Bnorm : ℝ)(hB : 0≤Bnorm)(budget : ℕ) : ℝ :=
  Classical.choose (eventual_actual_selected_old_rows_paid hB budget 3 (by norm_num))

def actualSelectedOldConstant_pos (Bnorm : ℝ)(hB : 0≤Bnorm)(budget : ℕ) :
    0<actualSelectedOldConstant Bnorm hB budget :=
  (Classical.choose_spec (eventual_actual_selected_old_rows_paid hB budget 3 (by norm_num))).1

/-- Genuine native absolute-box constant at the SAME post-dictionary rate. -/
def actualSelectedOldBoxConstant (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ) : ℝ :=
  Classical.choose (eventual_actual_geometry_main_absolute_box Nrow 4 (nativeMu/8) (9/4) (9/4)
    (nativeMu/64) (postDictionaryRate Bnorm budget) (by norm_num)
    (div_pos nativeMu_pos (by norm_num)) (by norm_num) (by norm_num)
    (div_nonneg nativeMu_pos.le (by norm_num)) (by nlinarith [nativeMu_pos]) (postDictionaryRate_budgets hB budget).1)

theorem actualSelectedOldBoxConstant_pos (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ) :
    0<actualSelectedOldBoxConstant Bnorm hB budget Nrow :=
  (Classical.choose_spec (eventual_actual_geometry_main_absolute_box Nrow 4 (nativeMu/8)
    (9/4) (9/4) (nativeMu/64) (postDictionaryRate Bnorm budget) (by norm_num)
    (div_pos nativeMu_pos (by norm_num)) (by norm_num) (by norm_num)
    (div_nonneg nativeMu_pos.le (by norm_num)) (by nlinarith [nativeMu_pos])
    (postDictionaryRate_budgets hB budget).1)).1

/-- Combine only genuine native source events: selected OLD payment,
physical dyad-box count/membership, and every first-child source radius. -/
def actualSelectedOldEvent (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ) :=
  let hold:=(Classical.choose_spec (eventual_actual_selected_old_rows_paid hB budget 3 (by norm_num))).2
  let hbox:=(Classical.choose_spec (eventual_actual_geometry_main_absolute_box Nrow 4 (nativeMu/8)
    (9/4) (9/4) (nativeMu/64) (postDictionaryRate Bnorm budget) (by norm_num)
    (div_pos nativeMu_pos (by norm_num)) (by norm_num) (by norm_num)
    (div_nonneg nativeMu_pos.le (by norm_num)) (by nlinarith [nativeMu_pos]) (postDictionaryRate_budgets hB budget).1)).2
  let hchild:=eventual_geometry_child_source_cap Nrow (9/4) (9/4) (nativeMu/8)
    (by norm_num) (by norm_num) (div_pos nativeMu_pos (by norm_num))
  (hold.and hbox).and hchild

def actualSelectedOldThreshold (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ) : ℝ :=
  Classical.choose (eventually_atTop.mp (actualSelectedOldEvent Bnorm hB budget Nrow))

/-- The true native payment and both structural source producers after
one threshold fixed before the character, native labels, ledger and row. -/
def actualSelectedOldAfter (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ)
    (Z : ℝ)(hZ : actualSelectedOldThreshold Bnorm hB budget Nrow≤Z) :=
  Classical.choose_spec (eventually_atTop.mp (actualSelectedOldEvent Bnorm hB budget Nrow)) Z hZ

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.actualSelectedOldAfter
