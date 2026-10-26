/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.FullGainBins
import Submissions.hailey_collet_1252270103.Record12518109Natural.ExceptionalHighGain

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
open LocalMoment
noncomputable section
inductive HighSector where
  | regular | fixed | tiny
  deriving DecidableEq

def sectorHighLower (sector : HighSector) (qlo : ℝ) : ℝ :=
  match sector with | .regular=>qlo | .fixed=>0 | .tiny=>0

def sectorHighGain (sector : HighSector) (ν S tinyCut q : ℝ) : ℝ :=
  match sector with
  | .regular=>Record12518109Gain.gain ν S q
  | .fixed=>exceptionalHighGain true ν S tinyCut q
  | .tiny=>exceptionalHighGain false ν S tinyCut q

lemma sector_high_gain_monotone (sector : HighSector)(ν S tinyCut : ℝ)
    (hν : 31/50≤ν)(hν' : ν≤3/4) : Monotone (sectorHighGain sector ν S tinyCut) := by
  cases sector
  · exact fun _ _ h=>Record12518109Gain.gain_mono hν hν' le_rfl h
  · exact exceptional_high_gain_monotone true ν S tinyCut hν'
  · exact exceptional_high_gain_monotone false ν S tinyCut hν'
end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.sector_high_gain_monotone
