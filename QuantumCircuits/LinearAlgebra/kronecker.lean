import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.QuantumCircuits.QuantumGates.qubit

open Complex
open scoped Matrix BigOperators

/-- Pure tensor (Kronecker) of two 1-qubit vectors as a 2-qubit vector. -/
@[simp] noncomputable def tensorVec (v w : Bit → ℂ) : (Bit × Bit) → ℂ :=
  fun ⟨x,y⟩ => v x * w y

/-- Kronecker-on-vectors, second wire:
    `(I ⊗ g)` acting on `v ⊗ w` equals `v ⊗ (g • w)`. -/
@[simp] lemma onSecond_mulVec_tensor (g : 𝐔[Bit]) (v w : Bit → ℂ) :
  (Qubit.onSecond g).val.mulVec (tensorVec v w)
  = tensorVec v (g.val.mulVec w) := by
  classical
  sorry


/-- Kronecker-on-vectors, first wire:
    `(g ⊗ I)` acting on `v ⊗ w` equals `(g • v) ⊗ w`. -/
@[simp] lemma onFirst_mulVec_tensor (g : 𝐔[Bit]) (v w : Bit → ℂ) :
  (Qubit.onFirst g).val.mulVec (tensorVec v w)
  = tensorVec (g.val.mulVec v) w := by
  classical
  sorry
