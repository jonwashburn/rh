import Mathlib.Data.Real.Basic
import rh.Cert.KxiPPlus
import rh.Cert.K0PPlus
import rh.Cert.KxiWhitney_RvM

noncomputable section

namespace RH.AcademicFramework.Certificate

/-! Certificate capabilities availability flags -/

/-- Availability of the analytic Kξ bound: delegated to the Whitney–box
Carleson interface provided by the `KxiWhitney_RvM` provider. -/
def KxiAvailable : Prop := ∃ α c : ℝ, RH.Cert.KxiWhitney.KxiBound α c

/-- Availability of the arithmetic tail nonnegativity `K0 ≥ 0` from the proved lemma. -/
def K0Available : Prop := RH.Cert.K0Available

/-- Readiness flag for certificate chain hooks: both `K0` and `Kξ` are available. -/
def Ready : Prop := K0Available ∧ KxiAvailable

/-- From a functional‑equation closed‑strip factors witness, we can still
obtain `KxiAvailable` via the Whitney–box provider (interface level). -/
theorem KxiAvailable_of_factors
    (h : Nonempty RH.Cert.FunctionalEquationStripFactors) :
    KxiAvailable := by
  -- We ignore the specific witness and use the RvM export at any parameters.
  exact ⟨(1 : ℝ), (1 : ℝ), RH.Cert.KxiWhitneyRvM.kxi_whitney_carleson_of_rvm 1 1⟩

/-- Proven availability of `Kξ`: use the RvM export at concrete parameters. -/
theorem KxiAvailable_proved : KxiAvailable :=
  ⟨(1 : ℝ), (1 : ℝ), RH.Cert.KxiWhitneyRvM.kxi_whitney_carleson_of_rvm 1 1⟩

/-- If `K0Available` holds and a factors witness exists, the certificate
track is ready (modulo the `CertificateReady` flag exposed by `rh/Cert`). -/
theorem Ready_of_factors
    (hK0 : K0Available)
    (hfac : Nonempty RH.Cert.FunctionalEquationStripFactors) : Ready := by
  refine And.intro hK0 ?hKxi
  exact KxiAvailable_of_factors hfac

/-- Unconditional readiness: combine arithmetic-tail availability with a
Whitney–box `Kξ` witness from the RvM provider. -/
theorem Ready_unconditional : Ready := by
  refine And.intro ?hK0 ?hKxi
  · exact RH.Cert.K0Available_proved
  · exact KxiAvailable_proved

end RH.AcademicFramework.Certificate
