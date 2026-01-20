import Mathlib
import MyNewProject.Intuitionism.fin_seq
import MyNewProject.Intuitionism.fan
import MyNewProject.Intuitionism.IPC


namespace IPC

/-- Encode (n,m,k) into ℕ by putting (n,m) into base part and k into mod 3 part. -/
def schedEncode : (ℕ × ℕ × Fin 3) → ℕ
| ⟨n,m,k⟩ => 3 * Nat.pair n m + k.1

/-- Decode ℕ back into (n,m,k) by div/mod 3 and unpair. -/
def schedDecode (t : ℕ) : (ℕ × ℕ × Fin 3) :=
  let q := t / 3
  let r := t % 3
  let nm := Nat.unpair q
  ⟨nm.1, nm.2, ⟨r, Nat.mod_lt _ (by decide : 0 < 3)⟩⟩

/-- easier direction: encode (decode t) = t -/
theorem schedEncode_decode (t : ℕ) :
    schedEncode (schedDecode t) = t := by
  -- q := t/3, r := t%3, nm := unpair q, then pair (unpair q)=q
  -- and div_add_mod gives q*3 + r = t
  simp [schedEncode, schedDecode, Nat.pair_unpair, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
        Nat.div_add_mod]

/-- harder direction: decode (encode x) = x -/
theorem schedDecode_encode (x : ℕ × ℕ × Fin 3) :
    schedDecode (schedEncode x) = x := by
  rcases x with ⟨n, m, k⟩
  set p : ℕ := Nat.pair n m
  have hk : (k.1 : ℕ) < 3 := k.2

  -- remainder: (3*p + k) % 3 = k
  have hmod : (3 * p + k.1) % 3 = k.1 := by
    calc
      (3 * p + k.1) % 3 = (k.1 + 3 * p) % 3 := by
        -- commute the addition
        simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = (k.1 % 3) := by
        -- (a + b*c) % b = a % b
        -- here b=3, a=k.1, c=p
        simp [Nat.add_mul_mod_self_left, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = k.1 := by
        simp [Nat.mod_eq_of_lt hk]

  -- quotient: (3*p + k) / 3 = p
  have hdiv : (3 * p + k.1) / 3 = p := by
    calc
      (3 * p + k.1) / 3 = (k.1 + 3 * p) / 3 := by
        simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = (k.1 / 3 + p) := by
        -- (a + b*c) / b = a/b + c
        -- here b=3, a=k.1, c=p
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        sorry
      _ = p := by
        simp [Nat.div_eq_of_lt hk]

  -- now unfold decode(encode ...) and compare components
  ext
  · -- first component = n
    simp [schedDecode, schedEncode, p, hdiv, Nat.unpair_pair]
  · simp
    · -- second component = m
      simp [schedDecode, schedEncode, p, hdiv, Nat.unpair_pair]
  simp
  simp [schedDecode, schedEncode, p, hdiv, Nat.unpair_pair]

/-- The equivalence (ℕ×ℕ×Fin3) ≃ ℕ. -/
noncomputable def schedEquiv : (ℕ × ℕ × Fin 3) ≃ ℕ :=
{ toFun := schedEncode
  invFun := schedDecode
  left_inv := schedDecode_encode
  right_inv := schedEncode_decode }

/-! ### Alignment property (Veldman-style) -/

def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩

/-- Alignment: <<n,m,0>>+2 = <<n,m,1>>+1 = <<n,m,2>>. -/
lemma sched_align (n m : ℕ) :
    (schedEncode ⟨n, m, k0⟩ + 2 = schedEncode ⟨n, m, k1⟩ + 1) ∧
    (schedEncode ⟨n, m, k1⟩ + 1 = schedEncode ⟨n, m, k2⟩) := by
  -- just arithmetic: 3*pair n m + 0 + 2 = 3*pair n m + 1 + 1 = 3*pair n m + 2
  constructor <;> simp [schedEncode, k0, k1, k2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  sorry
  sorry

end IPC
