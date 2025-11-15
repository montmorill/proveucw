import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finmap

section Vertex

structure Vertex where
  index : Option Nat
deriving DecidableEq

instance : OfNat Vertex N where
  ofNat := ⟨some N⟩

instance : ToString Vertex where
  toString v := match v with
    | ⟨none⟩ => "ω"
    | ⟨some index⟩ => s!"{index}"

abbrev ω : Vertex := ⟨none⟩

end Vertex

section Edge

structure Edge where
  lock : Option Nat
deriving DecidableEq

instance : OfNat Edge N where
  ofNat := ⟨some N⟩

instance : ToString Edge where
  toString e := match e with
    | ⟨none⟩ => "~~"
    | ⟨some lock⟩ => s!"~L({lock})~"

end Edge

section Chain

structure Chain where
  vertices : List Vertex
  edges : List Edge
  valid : vertices.length = edges.length + 1
deriving DecidableEq

def Chain.singleton (v : Vertex) : Chain :=
  ⟨[v], [], by simp⟩

def Chain.head (chain : Chain) : Vertex :=
  chain.vertices[0]'(by simp [chain.valid])

def Chain.last (chain : Chain) : Vertex :=
  chain.vertices[chain.vertices.length - 1]'(by simp [chain.valid])

instance : Coe Vertex Chain where
  coe := Chain.singleton

instance : OfNat Chain N where
  ofNat := Chain.singleton (OfNat.ofNat N)

instance : ToString Chain where
  toString chain :=
    (chain.edges.zipWith (ToString.toString · ++ ToString.toString ·) chain.vertices.tail)
    |>.foldl (· ++ ·) (ToString.toString (chain.head))

def Chain.append (chain : Chain) (v : Vertex) (e : Edge := ⟨none⟩) : Chain :=
  ⟨chain.vertices ++ [v], chain.edges ++ [e], by simp [chain.valid]⟩

def Chain.reverse (chain : Chain) : Chain :=
  ⟨chain.vertices.reverse, chain.edges.reverse, by simp [chain.valid]⟩

theorem Chain.reverse_reverse (chain : Chain) : chain.reverse.reverse = chain := by
  unfold Chain.reverse
  simp

def Chain.concat (a b : Chain) (_ : a.last = b.head) : Chain :=
  ⟨a.vertices ++ b.vertices.tail, a.edges ++ b.edges,
    by simp [List.length_append, a.valid, b.valid]; omega⟩

def Chain.is_lockless (chain : Chain) : Prop :=
  chain.edges.all (·.lock = none)

instance : Decidable (Chain.is_lockless chain) := by
  unfold Chain.is_lockless
  infer_instance

def Chain.is_subchain_of' (a b : Chain) : Prop :=
  ∃ (start : Fin (b.vertices.length - a.vertices.length + 1)),
    a.vertices = (b.vertices.drop start).take a.vertices.length ∧
    a.edges = (b.edges.drop start).take a.edges.length

def Chain.is_subchain_of (a b : Chain) : Prop :=
  Chain.is_subchain_of' a b ∨ Chain.is_subchain_of' a.reverse b

instance : Decidable (Chain.is_subchain_of a b) := by
  unfold Chain.is_subchain_of
  unfold Chain.is_subchain_of'
  infer_instance

notation:65 chain:65 " ~~ " vertex:66 => Chain.append chain vertex
notation:65 chain:65 " ~L(" lock ")~ " vertex:66 => Chain.append chain vertex lock

instance ChainSetoid : Setoid Chain where
  r a b := a = b ∨ a = b.reverse
  iseqv := {
    refl a := Or.inl rfl
    symm := by
      rintro a b (rfl|h)
      · left;  rfl
      · right; rw [h, Chain.reverse_reverse]
    trans := by
      rintro a b c (rfl|h₁) (rfl|h₂)
      · left;  rfl
      · right; exact h₂
      · right; rw [h₁]
      · left; rw [h₁, h₂, Chain.reverse_reverse]
  }

abbrev UndirectedChain := Quotient ChainSetoid

instance : Coe Chain UndirectedChain where
  coe := Quotient.mk'

instance (a b : Chain) : Decidable (a ≈ b) := by
  unfold HasEquiv.Equiv instHasEquivOfSetoid ChainSetoid
  simp; infer_instance

instance : DecidableEq UndirectedChain := inferInstance

abbrev ChainSet := Multiset UndirectedChain

instance : Singleton Chain ChainSet where
  singleton chain := {⟦chain⟧}

instance : Insert Chain ChainSet where
  insert chain chains := ⟦chain⟧ ::ₘ chains

end Chain

section Item

inductive Item where
  | Key (key : Nat) : Item
  | KeyOnce (key : Nat) : Item
deriving DecidableEq

notation:arg " K(" key ") " => Item.Key key
notation:arg " K*(" key ") " => Item.KeyOnce key

abbrev ItemSet := { x : Multiset Item // x ≠ ∅ }

instance : Singleton Item ItemSet where
  singleton item := ⟨Multiset.ofList [item], by simp⟩

instance : Insert Item ItemSet where
  insert item items := ⟨item ::ₘ items, by simp⟩

syntax "‹ " withoutPosition(term " ~ " term),* " ›" : term

macro_rules
  | `(‹ $[$k:term ~ $v:term],* ›) =>
    `([ $[Sigma.mk $k $v],* ].toAList.toFinmap)

abbrev ItemMap := Finmap (fun (_ : Vertex) ↦ ItemSet)

end Item
