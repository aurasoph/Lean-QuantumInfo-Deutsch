import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.QuantumCircuits.QuantumGates.qubit
import QuantumInfo.QuantumCircuits.QuantumGates.arithmetic
import QuantumInfo.QuantumCircuits.QuantumStates.measurement

open Complex
open scoped Matrix BigOperators

noncomputable section

namespace Deutsch

abbrev Bit := Qubit

/-- Pure tensor (Kronecker) of two 1-qubit vectors as a 2-qubit vector. -/
@[simp] noncomputable def tensorVec (v w : Bit → ℂ) : (Bit × Bit) → ℂ :=
  fun ⟨x,y⟩ => v x * w y

/-- Deutsch oracle as a permutation matrix on the computational basis. -/
noncomputable def Uf (f : Bit → Bit) : 𝐔[Bit × Bit] :=
  ⟨ Matrix.of (fun (p q : Bit × Bit) =>
      let x := p.1; let y := p.2; let x' := q.1; let y' := q.2
      if (x', y') = (x, Qubit.xor y (f x)) then (1 : ℂ) else 0),
    by
      sorry ⟩

@[simp] lemma Uf_apply (f : Bit → Bit) (x y x' y' : Bit) :
  Uf f (x, y) (x', y') =
    (if (x', y') = (x, Qubit.xor y (f x)) then (1 : ℂ) else 0) := rfl

@[simp] lemma Uf_hits (f : Bit → Bit) (x y : Bit) :
  Uf f (x, y) (x, Qubit.xor y (f x)) = 1 := by
  simp [Uf_apply]

@[simp] lemma Uf_miss (f : Bit → Bit) (x y x' y' : Bit)
    (h : (x', y') ≠ (x, Qubit.xor y (f x))) :
    Uf f (x, y) (x', y') = 0 := by
  classical
  by_cases hx : x' = x
  ·
    have hy : y' ≠ Qubit.xor y (f x) := by
      intro hy'
      apply h
      cases hx; cases hy'; rfl
    simp [Uf_apply, hx]
    simpa [Qubit.xor] using hy
  ·
    have hxy : (x', y') ≠ (x, Qubit.xor y (f x)) := by
      intro h'; exact hx (congrArg Prod.fst h')
    simp [Uf_apply, hxy]
    intro hx'
    exact (hx hx').elim

/-- The “balancedness” bit used by Deutsch’s decision rule. -/
@[simp] def bal (f : Bit → Bit) : Bit := Qubit.xor (f 0) (f 1)

/-- Global (physically irrelevant) phase used in the final state. -/
@[simp] def phase0 (f : Bit → Bit) : ℂ := if f 0 = 0 then 1 else -1


/-- Kronecker-on-vectors, second wire:
    `(I ⊗ g)` acting on `v ⊗ w` equals `v ⊗ (g • w)`. -/
@[simp] lemma onSecond_mulVec_tensor (g : 𝐔[Bit]) (v w : Bit → ℂ) :
  (Qubit.onSecond g).val.mulVec (tensorVec v w)
  = tensorVec v (g.val.mulVec w) := by
  classical
  -- Proof outline (to fill later):
  --  • expand mulVec: (A•u)(i) = ∑ j A i j * u j
  --  • use `Fintype.sum_prod_type` to split the product index Bit×Bit
  --  • `(onSecond g)(x,y)(x',y') = δ_{x,x'} * g y y'` (from kron with identity)
  --  • the δ kills the x'-sum, factor out `v x`, remaining y'-sum is `(g•w) y`
  --  • conclude `v x * (g•w) y = (v ⊗ (g•w))(x,y)`
  sorry


/-- Kronecker-on-vectors, first wire:
    `(g ⊗ I)` acting on `v ⊗ w` equals `(g • v) ⊗ w`. -/
@[simp] lemma onFirst_mulVec_tensor (g : 𝐔[Bit]) (v w : Bit → ℂ) :
  (Qubit.onFirst g).val.mulVec (tensorVec v w)
  = tensorVec (g.val.mulVec v) w := by
  classical
  -- Outline to fill later:
  --  • expand mulVec: (A•u)(i) = ∑ j A i j * u j
  --  • split index Bit×Bit, use (onFirst g)(x,y)(x',y') = g x x' * δ_{y,y'}
  --  • the δ kills the y'-sum, factor out (g•v) x; remaining is w y
  --  • result: ((g•v) ⊗ w)(x,y)
  sorry

/-- **Phase kickback on |−⟩.**
`Uf` acting on `v ⊗ |−⟩` multiplies the first-wire amplitude by `(-1)^{f x}`. -/
@[simp] lemma Uf_on_tensor_minus (f : Bit → Bit) (v : Bit → ℂ) :
  (Uf f).val.mulVec (tensorVec v Qubit.ketMinus_vec)
    = tensorVec (fun x => (if f x = 0 then 1 else -1) * v x) Qubit.ketMinus_vec := by
  classical
  -- Outline for later:
  -- • expand `mulVec`; use the matrix entries of `Uf` to collapse the sum
  -- • use that `X` on `|−⟩` gives a minus sign, so the XOR adds a phase (-1)^{f x}
  -- • factor the result as `tensorVec (...) ketMinus_vec`
  sorry

/-- **One-qubit finisher.**
`H ⋅ diag((-1)^{f}) ⋅ H ⋅ |0⟩ = phase0(f) ⋅ |bal(f)⟩`. -/
@[simp] lemma H_diagH_on_ket0 (f : Bit → Bit) :
  ((Qubit.H : 𝐔[Bit]).val).mulVec
    (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x)
  = (fun x => (phase0 f : ℂ) * (if x = bal f then 1 else 0)) := by
  classical
  -- Textbook 2×2 calculation over Bit = {0,1}; we’ll fill this later.
  -- (cases h0 : f 0; cases h1 : f 1; then `simp`.)
  sorry

/-- Factor a global scalar from the first wire of a tensor. -/
@[simp] lemma tensorVec_const_mul (c : ℂ) (v w : Bit → ℂ) :
  tensorVec (fun x => c * v x) w
  = (fun p => c * tensorVec v w p) := by
  classical
  funext p; rcases p with ⟨x,y⟩
  simp [tensorVec, mul_left_comm, mul_assoc]

theorem deutsch_correct_up_to_phase (f : Bit → Bit) :
  let ψ :=
    (Qubit.onFirst Qubit.H).val.mulVec (
      (Uf f).val.mulVec (
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Qubit.onSecond Qubit.H).val.mulVec (tensorVec Qubit.ket0_vec Qubit.ket1_vec))))
  ψ = (fun p => phase0 f * tensorVec (fun x => if x = bal f then 1 else 0) Qubit.ketMinus_vec p) := by
  classical
  intro ψ

  -- Stage 1: (I ⊗ H) on |0⟩⊗|1⟩
  have v1 :
    (Qubit.onSecond Qubit.H).val.mulVec (tensorVec Qubit.ket0_vec Qubit.ket1_vec)
      = tensorVec Qubit.ket0_vec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec) := by
    simpa using
      onSecond_mulVec_tensor (Qubit.H) Qubit.ket0_vec Qubit.ket1_vec

  -- Stage 2a: apply (H ⊗ I) to the result of Stage 1 (structural congruence)
  have v2a :
      (Qubit.onFirst Qubit.H).val.mulVec
        ((Qubit.onSecond Qubit.H).val.mulVec (tensorVec Qubit.ket0_vec Qubit.ket1_vec))
    =
      (Qubit.onFirst Qubit.H).val.mulVec
        (tensorVec Qubit.ket0_vec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)) := by
    -- apply (H ⊗ I) • _ to both sides of v1
    exact congrArg (fun t => (Qubit.onFirst Qubit.H).val.mulVec t) v1

  -- Stage 2b: (H ⊗ I) acts on the tensor (first wire)
  have v2b :
      (Qubit.onFirst Qubit.H).val.mulVec
        (tensorVec Qubit.ket0_vec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec))
    =
      tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)
                ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec) := by
    simpa using
      onFirst_mulVec_tensor (Qubit.H) Qubit.ket0_vec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)


  -- Stage 2c: rewrite H|1⟩ as |−⟩ on the second wire
  have v2c :
      tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)
                ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)
    =
      tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)
                Qubit.ketMinus_vec := by
    -- definition of |−⟩ is H|1⟩
    simp [Qubit.ketMinus_vec]

  -- Stage 3: Uf kickback on |−⟩
  have v3 :
      (Uf f).val.mulVec
        (tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) Qubit.ketMinus_vec)
    =
      tensorVec
        (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x)
        Qubit.ketMinus_vec := by
    simpa using
      Uf_on_tensor_minus f ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)

  -- Stage 4: final (H ⊗ I) on the first wire
  have v4 :
      (Qubit.onFirst Qubit.H).val.mulVec
        (tensorVec
          (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x)
          Qubit.ketMinus_vec)
    =
      tensorVec
        ((Qubit.H : 𝐔[Bit]).val.mulVec
          (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x))
        Qubit.ketMinus_vec := by
    simpa using
      onFirst_mulVec_tensor (Qubit.H)
        (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x)
        Qubit.ketMinus_vec

  -- Stage 5: collapse the first wire to phase0(f) · |bal(f)⟩
  have v5 :
      tensorVec
        ((Qubit.H : 𝐔[Bit]).val.mulVec
          (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x))
        Qubit.ketMinus_vec
    =
      (fun p => phase0 f * tensorVec (fun x => if x = bal f then 1 else 0) Qubit.ketMinus_vec p) := by
    classical
    -- Rewrite the first wire with the one-qubit finisher
    have hw :
      ((Qubit.H : 𝐔[Bit]).val.mulVec
        (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x))
      = (fun x => (phase0 f : ℂ) * (if x = bal f then 1 else 0)) := by
      simpa using H_diagH_on_ket0 f

    calc
      tensorVec
        ((Qubit.H : 𝐔[Bit]).val.mulVec
          (fun x => (if f x = 0 then 1 else -1) * ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x))
        ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)
          =
        tensorVec
          (fun x => (phase0 f : ℂ) * (if x = bal f then 1 else 0))
          ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec) := by
            exact
              (congrArg (fun v => tensorVec v ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)) hw)
      _ = (fun p =>
            phase0 f * tensorVec (fun x => if x = bal f then 1 else 0)
                                  ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec) p) := by
            simpa using
              tensorVec_const_mul (phase0 f)
                (fun x => if x = bal f then 1 else 0)
                ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)

  -- Stitch all stages inside ψ
  have unfoldψ :
      ψ
        =
      (Qubit.onFirst Qubit.H).val.mulVec (
        (Uf f).val.mulVec (
          (Qubit.onFirst Qubit.H).val.mulVec (
            (Qubit.onSecond Qubit.H).val.mulVec (tensorVec Qubit.ket0_vec Qubit.ket1_vec)))) := rfl

  -- One final equality chaining all intermediate steps to the desired RHS
  -- Final stitching: push v1 → v2a → v2b → v2c → v3 → v4 → v5 through the nested mulVecs
  have hfinal :
      (Qubit.onFirst Qubit.H).val.mulVec (
        (Uf f).val.mulVec (
          (Qubit.onFirst Qubit.H).val.mulVec (
            (Qubit.onSecond Qubit.H).val.mulVec (tensorVec Qubit.ket0_vec Qubit.ket1_vec))))
    =
      (fun p => phase0 f * tensorVec (fun x => if x = bal f then 1 else 0) Qubit.ketMinus_vec p) := by
    have w1 :
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Uf f).val.mulVec (
            (Qubit.onFirst Qubit.H).val.mulVec (
              (Qubit.onSecond Qubit.H).val.mulVec (tensorVec Qubit.ket0_vec Qubit.ket1_vec))))
      =
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Uf f).val.mulVec (
            (Qubit.onFirst Qubit.H).val.mulVec (
              tensorVec Qubit.ket0_vec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)))) := by
      exact congrArg (fun t =>
        (Qubit.onFirst Qubit.H).val.mulVec ((Uf f).val.mulVec ((Qubit.onFirst Qubit.H).val.mulVec t))) v1

    -- use v2b to compute (onFirst H) on that tensor (still under (Uf f))
    have w2 :
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Uf f).val.mulVec (
            (Qubit.onFirst Qubit.H).val.mulVec (
              tensorVec Qubit.ket0_vec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec))))
      =
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Uf f).val.mulVec (
            tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)
                      ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec))) := by
      exact congrArg (fun t =>
        (Qubit.onFirst Qubit.H).val.mulVec ((Uf f).val.mulVec t)) v2b

    -- rewrite second wire H|1⟩ as |−⟩ (v2c), still under (Uf f) then (onFirst H)
    have w3 :
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Uf f).val.mulVec (
            tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)
                      ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket1_vec)))
      =
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Uf f).val.mulVec (
            tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)
                      Qubit.ketMinus_vec)) := by
      exact congrArg (fun t =>
        (Qubit.onFirst Qubit.H).val.mulVec ((Uf f).val.mulVec t)) v2c

    -- apply Uf kickback (v3), then leave outer (onFirst H) for next step
    have w4 :
        (Qubit.onFirst Qubit.H).val.mulVec (
          (Uf f).val.mulVec (
            tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec)
                      Qubit.ketMinus_vec))
      =
        (Qubit.onFirst Qubit.H).val.mulVec (
          tensorVec (fun x => (if f x = 0 then 1 else -1) *
                              ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x)
                    Qubit.ketMinus_vec) := by
      exact congrArg (fun t => (Qubit.onFirst Qubit.H).val.mulVec t) v3

    -- push the final (onFirst H) over the tensor (v4)
    have w5 :
        (Qubit.onFirst Qubit.H).val.mulVec (
          tensorVec (fun x => (if f x = 0 then 1 else -1) *
                              ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x)
                    Qubit.ketMinus_vec)
      =
        tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec
                    (fun x => (if f x = 0 then 1 else -1) *
                              ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x))
                  Qubit.ketMinus_vec := by
      exact v4

    -- collapse the first wire to phase0(f) · |bal f⟩ (v5)
    have w6 :
        tensorVec ((Qubit.H : 𝐔[Bit]).val.mulVec
                    (fun x => (if f x = 0 then 1 else -1) *
                              ((Qubit.H : 𝐔[Bit]).val.mulVec Qubit.ket0_vec) x))
                  Qubit.ketMinus_vec
      =
        (fun p => phase0 f * tensorVec (fun x => if x = bal f then 1 else 0) Qubit.ketMinus_vec p) := by
      exact v5

    -- chain all rewrites
    exact Eq.trans w1 (Eq.trans w2 (Eq.trans w3 (Eq.trans w4 (Eq.trans w5 w6))))

  simpa [unfoldψ] using hfinal


end Deutsch
