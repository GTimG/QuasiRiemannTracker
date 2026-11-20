/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original profile control for every genuine canonical restored pair source. -/
import Candidate.C092.transport.TwistedRawBallCanonicalMarks
import Submissions.sil_density_split_20261026.CubeFree.FP.RepairedSourceProfiles
set_option autoImplicit false
namespace QRH.Cycle092.OrderedPairActualRestored
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentSourceProfileMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedOriginalTail RepairedSourceSideSupply
open QRH.Cycle092.TwistedRawBallRootProducer
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {ι:Type*} [Fintype ι]

theorem profile_cap_sq (s:Source ι (1/4) (9/4)) (N:ℕ) (hcard:Fintype.card ι≤N)
    (K:ℝ) (hK:1≤K) (hM:∀i,s.M i≤K) (p:Profiles (1/4) (9/4))
    (hp₁:s.W₁=p.profile 0) (hp₂:s.W₂=p.profile 1)
    (controls:Finset (ℕ×ℕ)) (h00:(0,0)∈controls) :
    (profileCap s)^2≤(4*K^(2*N))*(p.control controls)^2 := by
  have h:=RepairedSourceProfiles.profileCap_sq_le_amplitude s N hcard K hK hM
    0 0 (by norm_num) 0 controls h00 1 le_rfl
  unfold amplitude at h
  rw [hp₁,hp₂] at h
  simpa only [pow_zero,one_mul,mul_one,Profiles.control] using h

section Canonical
variable (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
variable (hHr:RayOrthogonality.globalUnits M≤Hr) (r:RestoredRootSource.Data M Hr ι)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)
variable (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
variable (hprod:X₁*X₂=Y₁*Y₂)
variable (hx₁:X₁≤r.Z) (hx₂:X₂≤r.Z) (hy₁:Y₁≤r.Z) (hy₂:Y₂≤r.Z)
local notation "s"=>canonicalPairSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂
  hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂

theorem canonical_profile_cap_sq (N:ℕ) (hcard:Fintype.card ι≤N)
    (controls:Finset (ℕ×ℕ)) (h00:(0,0)∈controls) :
    (profileCap s)^2≤
      (4*(RestoredRootSource.slotBound r.W r.hW r.hWs)^(2*N))*(r.p.control controls)^2 := by
  apply profile_cap_sq s N hcard _ (RestoredRootSource.slotBound_spec r.W r.hW r.hWs).1
    (fun i=>le_rfl) r.p rfl rfl controls h00
end Canonical

#print axioms profile_cap_sq
#print axioms canonical_profile_cap_sq
end
end QRH.Cycle092.OrderedPairActualRestored
