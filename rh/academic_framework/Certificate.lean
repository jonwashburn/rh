import rh.Cert.KxiPPlus
import rh.Cert.FactorsWitness
import rh.Cert.K0PPlus

noncomputable section

namespace RH.AcademicFramework.Certificate

/-! Certificate capabilities availability flags -/

/-- Availability of Kξ analytic bound via closed-strip functional-equation
factors: downstream tracks only need existence of a witness. -/
def KxiAvailable : Prop := Nonempty RH.Cert.FunctionalEquationStripFactors

/-- Availability of the arithmetic tail nonnegativity `K0 ≥ 0` from the proved lemma. -/
def K0Available : Prop := RH.Cert.K0Available

/-- Readiness flag for certificate chain hooks. -/
def Ready : Prop :=
  KxiAvailable ∧ K0Available ∧ RH.Cert.CertificateReady

/-- If `K0Available` holds and a factors witness exists, the certificate
track is ready (modulo the `CertificateReady` flag exposed by `rh/Cert`). -/
theorem Ready_of_factors
    (hK0 : K0Available)
    (hfac : Nonempty RH.Cert.FunctionalEquationStripFactors)
    (hCert : RH.Cert.CertificateReady) : Ready := by
  refine And.intro ?hKxi (And.intro hK0 hCert)
  exact hfac

/-- Unconditional readiness: combine arithmetic-tail availability with the
analytic factors witness and the trivial certificate flag. -/
theorem Ready_unconditional : Ready := by
  refine Ready_of_factors ?hK0 ?hFac ?hCert
  · -- arithmetic tail availability from proved lemma
    exact RH.Cert.K0Available_proved
  · -- analytic factors witness from FactorsWitness
    exact RH.Cert.factors_witness_nonempty
  · -- certificate flag is `True`
    exact (by trivial : RH.Cert.CertificateReady)

/-- From a functional-equation closed-strip factors witness, we get
`KxiAvailable`. -/
theorem KxiAvailable_of_factors
    (h : Nonempty RH.Cert.FunctionalEquationStripFactors) :
    KxiAvailable := h

end RH.AcademicFramework.Certificate
