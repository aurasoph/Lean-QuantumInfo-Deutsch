import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.QuantumCircuits.QuantumGates.basic

namespace Qubit


@[simp] def onFirst  (g : 𝐔[Bit]) : 𝐔[Bit × Bit] := Matrix.unitary_kron g (1 : 𝐔[Bit])
@[simp] def onSecond (g : 𝐔[Bit]) : 𝐔[Bit × Bit] := Matrix.unitary_kron (1 : 𝐔[Bit]) g
-- Lift a 1-qubit unitary `g` to a 2-qubit unitary by taking a Kronecker product:
--   onFirst g ≈ g ⊗ I
--   onSecond g ≈ I ⊗ g


@[simp] noncomputable def H₁ : 𝐔[Bit × Bit] := onFirst  (Qubit.H)
@[simp] noncomputable def H₂ : 𝐔[Bit × Bit] := onSecond (Qubit.H)

end Qubit
