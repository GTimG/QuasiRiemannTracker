/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The tiny branch uses the radial bin count and the external tiny cutoff. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.HighSector
set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
open LocalMoment
noncomputable section

def sectorSharpGain (sector : HighSector) (ν S tinyCut q : ℝ) : ℝ :=
  match sector with
  | .regular=>Record12518109Gain.gain ν S q
  | .fixed=>exceptionalHighGain true ν S tinyCut q
  | .tiny=>(unmarkedDensity ν-1)*tinyCut+(ν-1)*S

lemma sector_sharp_gain_monotone (sector : HighSector)(ν S tinyCut : ℝ)
    (hν : 31/50≤ν)(hν' : ν≤3/4) : Monotone (sectorSharpGain sector ν S tinyCut) := by
  cases sector
  · exact fun _ _ h=>Record12518109Gain.gain_mono hν hν' le_rfl h
  · exact exceptional_high_gain_monotone true ν S tinyCut hν'
  · exact fun _ _ _=>le_refl _

lemma tiny_radial_interpolation (ρ q Q : ℝ) (hρ : 0≤ρ) (hρ' : ρ≤1) :
    min q Q≤ρ*q+(1-ρ)*Q := by
  rcases le_total q Q with h|h
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right h]
    nlinarith
end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.tiny_radial_interpolation
