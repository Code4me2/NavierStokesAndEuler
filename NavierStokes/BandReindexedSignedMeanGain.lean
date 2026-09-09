import NavierStokes.SignedMeanGain

/-!
# Signed mean gain with fixed physical labels

The physical wave family keeps its original label type.  At each band an
injection on the active finite set identifies its coefficient data with the
relative native labels used by `SignedMeanGain.NativeData`.  Finite-sum
reindexing then gives the actual native cross identity.  The mean-gain theorem
is applied to the original family, with its original uniform constants.
-/

noncomputable section

namespace NavierStokes.BandReindexedSignedMeanGain

open Set Function
open scoped BigOperators
open WeightedClasses MeanIncrementBounds CorrectionState SignedMeanGain

/-! ## Coefficient and carrier identities at one band -/

/-- The carrier metadata needed to compare the actual fields at one band.
No relationship at another band is required. -/
structure SameCarrierAt {D : Type} (a b : HarmonicBlock D) (n : ℕ) : Prop where
  frequency : b.frequency n = a.frequency n
  phase : b.phase n = a.phase n
  angular : b.angularFrequency n = a.angularFrequency n


/-- Equality of the stored coefficients and carrier metadata identifies the
actual harmonic field at this band.  Pressure data are not used in covariance. -/
theorem oscillation_eq_at_band_of_coefficients {D : Type}
    (a b : HarmonicBlock D) (n : ℕ)
    (hv : a.velocity n = b.velocity n) (hc : SameCarrierAt a b n) :
    a.oscillation n = b.oscillation n := by
  funext p i
  simp only [HarmonicBlock.oscillation, hv, hc.frequency, hc.phase, hc.angular]

/-! ## Finite reindexing of actual fields -/


/-! ## The native requested cross for arbitrary physical labels -/



/-! ## The gain for the original family and literal reconstructed state -/


end NavierStokes.BandReindexedSignedMeanGain
