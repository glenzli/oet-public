import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.chain_propagation
import formal_oet.vol_01.ch_05_operator_networks.path_matrix

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

noncomputable section

theorem right_chain_lip_bounded_of_certificate_list
    {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal}
    {operators : List (Operator X bot)} {U : Set X}
    {matrices : List (I → I → ENNReal)}
    (h : RightChainLipCertificateList d operators U matrices) :
    RightChainLipBounded d operators U (matrix_list_mul matrices) := by
  induction h with
  | nil U hU => exact RightChainLipBounded.nil U hU
  | cons ϕ tail U Lϕ Ls htail hϕ ih =>
      exact RightChainLipBounded.cons ϕ tail U Lϕ (matrix_list_mul Ls) ih hϕ

/-- Auxiliary composition of already established Lip bounds. The actual
derivative-to-path statements are in `occurrence_jacobi_bridge.lean`. -/
theorem occurrence_domain_lip_certificates_compose
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (operators : List (Operator X bot)) (U : Set X)
    (matrices : List (I → I → ENNReal))
    (h : RightChainLipCertificateList d operators U matrices) :
    IsLipMatrix d (OperatorChain operators) U (matrix_list_mul matrices) := by
  exact right_chain_lip_matrix d operators U (matrix_list_mul matrices)
    (right_chain_lip_bounded_of_certificate_list h)

end

end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
