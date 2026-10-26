/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The tiny sector is selected by the actual geometric frequency upper coordinate.
It therefore satisfies both the count cutoff and its scalar payment cutoff. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalFrequencyNonnegative
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.SharpHighSector
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open scoped Classical BigOperators

def selectedHighSector (core : Prop) [Decidable core] (q cutoff : ℝ) : HighSector :=
  if q≤cutoff then .tiny else if core then .fixed else .regular

theorem selected_high_sector_gates (core : Prop) [Decidable core]
    (Z q cutoff : ℝ) (hZ : 1<Z) (w : NonzeroFrequency)
    (hq : rawFrequencyNorm w≤Z^q) :
    0≤q ∧
    (selectedHighSector core q cutoff=.regular → ¬core ∧ cutoff≤q) ∧
    (selectedHighSector core q cutoff=.fixed → core) ∧
    (selectedHighSector core q cutoff=.tiny → q≤cutoff ∧ rawFrequencyNorm w≤Z^cutoff) := by
  refine ⟨raw_frequency_exponent_nonnegative Z q hZ w hq,?_,?_,?_⟩
  · unfold selectedHighSector
    split_ifs with hsmall hcore
    · intro h; cases h
    · intro h; cases h
    · exact fun _=>⟨hcore,(lt_of_not_ge hsmall).le⟩
  · unfold selectedHighSector
    split_ifs with hsmall hcore
    · intro h; cases h
    · exact fun _=>hcore
    · intro h; cases h
  · unfold selectedHighSector
    split_ifs with hsmall hcore
    · exact fun _=>⟨hsmall,hq.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hsmall)⟩
    · intro h; cases h
    · intro h; cases h

theorem selected_high_sector_sum {Row : Type} (rows : Finset Row)
    (core : Row→Prop) [DecidablePred core] (q : Row→ℝ) (cutoff : ℝ) (f : Row→ℝ) :
    ∑r∈rows,f r =
      (∑r∈rows.filter (fun r=>selectedHighSector (core r) (q r) cutoff=.regular),f r)+
      (∑r∈rows.filter (fun r=>selectedHighSector (core r) (q r) cutoff=.fixed),f r)+
      (∑r∈rows.filter (fun r=>selectedHighSector (core r) (q r) cutoff=.tiny),f r) := by
  classical
  simp only [Finset.sum_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  cases h:selectedHighSector (core r) (q r) cutoff <;> simp [h]

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_high_sector_gates
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_high_sector_sum
