import Std

instance [Inhabited ε] : Alternative (Except ε) where
  failure := Except.error default
  orElse f g := f.orElseLazy g

def Array.pmap [DecidableEq α] (A : Array α) (f : (a : α) → a ∈ A → β) : Array β :=
  Array.ofFn (fun (i : Fin A.size) => f (A[i]) sorry) -- the array interface is useless.

def Array.forall_of_all {A : Array α} (f : α → Bool) :
    A.all f → ∀ i : Fin A.size, f A[i] := by
  rintro h ⟨i,hi⟩
  have : A.all f i := by
    induction i with
    | zero => exact h
    | succ i ih =>
      have := ih (Nat.lt_of_succ_lt hi)
      simp [all, allM, Id.run, anyM] at this ⊢
      unfold anyM.loop at this
      simp [Nat.lt_of_succ_lt hi] at this
      split at this
      · contradiction
      · assumption
  simp [all, Id.run, allM, anyM] at this
  unfold anyM.loop at this
  simp [hi] at this
  split at this
  · contradiction
  · simp [*]

namespace Lean.RBNode

inductive Mem {α} {β : α → Type} : ((a : α) × β a) → RBNode α β → Prop
| here (a : α) (x : β a) : Mem ⟨a, x⟩ (.node c L a x R)
| left  : Mem a L → Mem a (.node c L a' x R)
| right : Mem a R → Mem a (.node c L a' x R)

instance : Membership ((a : α) × β a) (RBNode α β) := ⟨Mem⟩

def pmap (n : RBNode α β) (f : (a : α) → (b : β a) → ⟨a,b⟩ ∈ n → γ a) : RBNode α γ :=
  match n with
  | .node c L a x R =>
    .node c
      (pmap L (f · · <| .left ·))
      a (f a x (.here _ _))
      (pmap R (f · · <| .right ·))
  | .leaf => .leaf

theorem forall_of_all (n : RBNode α β) (h : n.all p) : ∀ a b, ⟨a,b⟩ ∈ n → p a b := by
  intro a b hab
  induction n with
  | leaf => cases hab
  | node c L a' b' R Lih Rih =>
    cases hab <;> simp [all] at h
    · exact h.1.1
    case left hab =>
      exact Lih h.1.2 hab
    case right hab =>
      exact Rih h.2 hab

theorem lt_sizeOf_of_mem (m : Lean.RBNode α β) [SizeOf α] [∀ a, SizeOf (β a)] {a : α} {b : β a} (h : ⟨a,b⟩ ∈ m)
  : sizeOf b < sizeOf m := by
  induction m with
  | leaf => contradiction
  | node c l k v r lih rih =>
    cases h <;> simp
    case here =>
      simp [Nat.add_comm _ (sizeOf b), Nat.add_assoc (sizeOf b)]
      apply Nat.lt_add_of_pos_right
      simp [Nat.add_assoc 1]; rw [Nat.add_comm]; apply Nat.succ_pos
    case left h =>
      apply Nat.lt_trans (lih h)
      rw [Nat.add_comm _ (sizeOf l), ←Nat.add_assoc _ 1]
      repeat (first | apply Nat.lt_succ_self | apply Nat.lt_add_right)
    case right h =>
      apply Nat.lt_trans (rih h)
      apply Nat.lt_add_of_pos_left
      simp [Nat.add_assoc 1]; rw [Nat.add_comm]; apply Nat.succ_pos

theorem keys_eq_of_findCore_some (m : Lean.RBNode α β) (h : m.findCore cmp a = some ⟨a',b⟩) : cmp a a' = .eq := by
  induction m with
  | leaf => simp [findCore] at h
  | node c l k v r lih rih =>
    simp [findCore] at h
    split at h
    · exact lih h
    · exact rih h
    · simp at h; cases h
      assumption

theorem mem_of_findCore (m : Lean.RBNode α β) (h : m.findCore cmp a = some ⟨a',b⟩) : ⟨a',b⟩ ∈ m := by
  induction m with
  | leaf => simp [findCore] at h
  | node c l k v r lih rih =>
    simp [findCore] at h
    split at h
    · exact .left <| lih h
    · exact .right <| rih h
    · simp at h; cases h
      apply Mem.here

end Lean.RBNode

instance [Inhabited α] [Inhabited β] : Inhabited ((_ : α) × β) where
  default := ⟨default, default⟩

open Std.Format in
def Lean.Json.reprPrec (j : Lean.Json) (prec : Nat) : Format :=
  match j with
  | .obj m =>
    let middle := m.fold (fun L s j' =>
      have : sizeOf j' < 1 + sizeOf m := sorry
      (group <|
        text ("\"" ++ s ++ "\"")
        ++ ": " ++
        reprPrec j' (prec+1))
      :: L
      ) []
    group <| nestD <| "{" ++ line ++ (join <| middle.intersperse ("," ++ line)) ++ "}"
  | .arr js =>
    let middle := js.map (fun j' =>
        have : sizeOf j' < 1 + sizeOf js := sorry
        reprPrec j' (prec+1))
      |>.toList
    group <| nestD <| "[" ++ (join <| middle.intersperse ("," ++ line)) ++ "]"
  | .str s => s.quote
  | .num n => toString n
  | .bool b => toString b
  | .null => "null"
termination_by _ j _ => sizeOf j

instance : Repr Lean.Json := ⟨Lean.Json.reprPrec⟩
