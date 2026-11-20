/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal M.4 native crossing and tails for the original Q source. -/
import Candidate.C092.transport.DirectGuardModels
import Candidate.C092.transport.DirectCountSource
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountFromMoments
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace QRH.Cycle092.DirectCount
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Record1252270103Return

/- This field identity is copied from Collet's CountAdmission because that
particular upstream object is absent from the approved import overlay. -/
private theorem crossing_algebra {δ p D A Z U J : ℝ}
    (hD : D=1-p+A) (hU : U=(1-p)*(1-Z))
    (hJ : J=(5/6-δ)*D+δ*(1-p)*A) (hD0 : D≠0) (hJ0 : J≠0) :
    1-δ*(p+(1-p)*((A*(J+δ*U)+(Z-p)*J)/(D*J)))=
      ((1-δ)*J+(5/6-δ)*δ*U)/J := by
  field_simp [hD0,hJ0]
  rw [hJ,hD,hU]
  ring

def nativeT (s δ p : ℝ) : ℝ := countJ .native s 0 δ p+δ*((1-p)*nativeC s p)
def nativeRN (s δ p : ℝ) : ℝ := nativeA s p*nativeT s δ p+
  ((1-nativeC s p)-p)*countJ .native s 0 δ p
def nativeMN (s δ p : ℝ) : ℝ := nativeD s p*nativeT s δ p-nativeRN s δ p
def nativeCutoff (s δ p : ℝ) : ℝ := nativeT s δ p/countJ .native s 0 δ p
def nativeCross (s δ p : ℝ) : ℝ := nativeRN s δ p/(nativeD s p*countJ .native s 0 δ p)
def nativePlain (s δ p : ℝ) : ℝ := nativeMN s δ p/(nativeD s p*countJ .native s 0 δ p)
def nativeValue (s δ p : ℝ) : ℝ := countN .native s 0 δ p/countJ .native s 0 δ p

theorem native_cross_identity (s δ p : ℝ) (hD : 0 < nativeD s p)
    (hJ : 0 < countJ .native s 0 δ p) :
    1-δ*(p+(1-p)*nativeCross s δ p)=nativeValue s δ p := by
  convert crossing_algebra (by dsimp [nativeD,nativeA]; ring)
    (by ring : (1-p)*nativeC s p=(1-p)*(1-(1-nativeC s p))) rfl hD.ne' hJ.ne' using 1 <;>
    dsimp [nativeCross,nativeRN,nativeValue,nativeT,countN,countJ] <;> ring

theorem native_lengths (s δ p : ℝ) (hD : 0 < nativeD s p)
    (hJ : 0 < countJ .native s 0 δ p) :
    nativeCross s δ p+nativePlain s δ p=nativeCutoff s δ p := by
  dsimp [nativeCross,nativePlain,nativeCutoff,nativeMN]
  field_simp [hD.ne',hJ.ne']
  ring

theorem native_plain_identity (s δ p : ℝ) (hD : 0 < nativeD s p)
    (hJ : 0 < countJ .native s 0 δ p) :
    1-δ*(nativeA s p)*nativePlain s δ p-δ*(1-nativeC s p)=nativeValue s δ p := by
  have hc := native_cross_identity s δ p hD hJ
  have hs := native_lengths s δ p hD hJ
  have hr : nativeD s p*nativeCross s δ p =
      nativeA s p*nativeCutoff s δ p+(1-nativeC s p)-p := by
    dsimp [nativeCross,nativeCutoff,nativeRN]
    field_simp [hD.ne',hJ.ne']
    ring
  have hD' : nativeD s p=1-p+nativeA s p := by dsimp [nativeD,nativeA]; ring
  have hd := congrArg (fun x => x*nativeCross s δ p) hD'
  have hh := congrArg (fun x => nativeA s p*x) hs
  have he : p+(1-p)*nativeCross s δ p=
      nativeA s p*nativePlain s δ p+(1-nativeC s p) := by nlinarith
  rw [he] at hc
  nlinarith

theorem native_long_identity (s δ p : ℝ) (hJ : 0 < countJ .native s 0 δ p) :
    1-δ+(5/6-δ)*(nativeCutoff s δ p-1)=nativeValue s δ p := by
  dsimp [nativeCutoff,nativeValue,nativeT,countN]
  field_simp [hJ.ne']
  ring

/-- The original source collar and the exact count-window fees remain present. -/
def nativeCap : ℝ := countFace.slotHi-1/10000000
def nativeLo : ℝ := nativeLower sourceCost-1/10000000
def nativeHi : ℝ := 1757/4000

structure NativeData (δ p : ℝ) : Prop where
  Dpos : 0 < nativeD sourceCost p
  Jpos : 0 < countJ .native sourceCost 0 δ p
  cutoffLo : 1 ≤ nativeCutoff sourceCost δ p
  cutoffHi : nativeCutoff sourceCost δ p ≤ 3/2
  crossLo : 23/37 ≤ nativeCross sourceCost δ p
  crossHi : nativeCross sourceCost δ p ≤ 1
  plainBuffer : nativeLo+1/10000000 ≤ nativeCutoff sourceCost δ p-nativeCross sourceCost δ p
  plainCrossing : plainCurve countFace.B countFace.lam nativeCap δ p
    (nativeCutoff sourceCost δ p-nativeCross sourceCost δ p) ≤ nativeValue sourceCost δ p
  tail : ∀ κ : ℝ, 7/10 ≤ κ → κ ≤ 3/4 →
    1-2*δ*nativeHi-2*(δ*p)*(1-2*nativeHi)/(6*κ) ≤ nativeValue sourceCost δ p
  widths : ∀ ν : ℝ, ν ≤ 1/10000000 → ∀ m : ℝ, nativeLo ≤ m → m ≤ nativeHi →
    ν < min nativeCap ((countFace.B-2*m)/countFace.lam)

theorem native_data {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p)
    (hg : ∀ j : Fin 15, 0 < nativeGuard j sourceCost δ p) : NativeData δ p := by
  have hD := hg 0
  change 0 < nativeD sourceCost p at hD
  have hJ := hg 3
  change 0 < countJ .native sourceCost 0 δ p at hJ
  have hDJ : 0 < nativeD sourceCost p*countJ .native sourceCost 0 δ p := mul_pos hD hJ
  have hTlo := hg 4
  change 0 < nativeT sourceCost δ p-countJ .native sourceCost 0 δ p at hTlo
  have hThi := hg 5
  change 0 < (12499/10000)*countJ .native sourceCost 0 δ p-nativeT sourceCost δ p at hThi
  have hrlo := hg 6
  change 0 < nativeRN sourceCost δ p-(23/37)*(nativeD sourceCost p*countJ .native sourceCost 0 δ p) at hrlo
  have hrhi := hg 7
  change 0 < nativeD sourceCost p*countJ .native sourceCost 0 δ p-nativeRN sourceCost δ p at hrhi
  have hmlo := hg 8
  change 0 < nativeMN sourceCost δ p-nativeLower sourceCost*(nativeD sourceCost p*countJ .native sourceCost 0 δ p) at hmlo
  have hml : nativeLower sourceCost < nativePlain sourceCost δ p :=
    (lt_div_iff₀ hDJ).mpr (by linarith)
  have hLam : 0 < countFace.lam := by
    change 0 < 2+10*sourceCost
    linarith [allowances_pos.1]
  have hs := source_contact_guards.1
  have hs' := source_contact_guards.2.1
  have hcap : (1/10000000 : ℝ) < nativeCap := by
    change 1/10000000 < 3/20-1000*sourceCost/1143-1/10000000
    linarith
  refine ⟨hD,hJ,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (lt_div_iff₀ hJ).mpr (by linarith) |>.le
  · dsimp [nativeCutoff]
    apply (div_le_iff₀ hJ).mpr
    linarith
  · exact ((lt_div_iff₀ hDJ).mpr (by linarith : (23/37)*(nativeD sourceCost p*countJ .native sourceCost 0 δ p)<nativeRN sourceCost δ p)).le
  · exact ((div_lt_iff₀ hDJ).mpr (by linarith : nativeRN sourceCost δ p<1*(nativeD sourceCost p*countJ .native sourceCost 0 δ p))).le
  · rw [show nativeCutoff sourceCost δ p-nativeCross sourceCost δ p=nativePlain sourceCost δ p by linarith [native_lengths sourceCost δ p hD hJ]]
    simpa only [nativeLo,sub_add_cancel] using hml.le
  · have hmcap : (countFace.B-2*nativePlain sourceCost δ p)/countFace.lam ≤ nativeCap := by
      apply (div_le_iff₀ hLam).mpr
      dsimp [nativeLo,nativeLower,nativeCap,countFace,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face] at *
      nlinarith
    rw [show nativeCutoff sourceCost δ p-nativeCross sourceCost δ p=nativePlain sourceCost δ p by linarith [native_lengths sourceCost δ p hD hJ],
      plainCurve_eq _ _ _ _ _ _ hδ hp,min_eq_right hmcap]
    have he := native_plain_identity sourceCost δ p hD hJ
    convert he.le using 1 <;> dsimp [nativeA,nativeC,countFace,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face] <;> ring
  · intro κ hk hk1
    have hκ : 0 < 6*κ := by linarith
    have hz : (27/1000 : ℝ) ≤ (1-2*nativeHi)/(6*κ) := by
      apply (le_div_iff₀ hκ).mpr
      norm_num [nativeHi]
      linarith
    have hh := hg 10
    change 0 < countN .native sourceCost 0 δ p-
      (1-2*δ*nativeHi-2*δ*p*(27/1000))*countJ .native sourceCost 0 δ p at hh
    have hv : 1-2*δ*nativeHi-2*δ*p*(27/1000) ≤ nativeValue sourceCost δ p :=
      (le_div_iff₀ hJ).mpr (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2*δ*p)
    calc
      _ = 1-2*δ*nativeHi-2*δ*p*((1-2*nativeHi)/(6*κ)) := by ring
      _ ≤ nativeValue sourceCost δ p := by linarith
  · intro ν hν m hm hm'
    apply lt_min (lt_of_le_of_lt hν hcap)
    apply (lt_div_iff₀ hLam).mpr
    have hh := hg 13
    change 0 < countFace.B-2*nativeHi-countFace.lam*(27/1000+1/10000000)-2/10000000 at hh
    have hn := mul_le_mul_of_nonneg_left hν hLam.le
    nlinarith
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.native_data
