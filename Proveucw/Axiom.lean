import Proveucw.Basic
import Proveucw.Tactics

opaque Beatable (chains : ChainSet) (items : ItemMap := ∅) : Prop

variable {chains : ChainSet} {items : ItemMap}

section Chapter1

axiom Axiom1 (chain : Chain) (items : ItemMap := ∅)
    (hhead : chain.head = 0 := by decide)
    (hlast : chain.last = ω := by decide)
    (hlockless : chain.is_lockless := by decide)
  :  Beatable {chain} items

theorem Prop1_1 : Beatable {0 ~~ 1 ~~ 2 ~~ ω} := by
  apply Axiom1 (0 ~~ 1 ~~ 2 ~~ ω)

axiom Rule1_1 (chain : Chain) (h : Beatable chains items)
  : Beatable (⟦chain⟧ ::ₘ chains) items

axiom Rule1_2 (sub super : Chain) (h : Beatable chains items)
    (hsubchain : sub.is_subchain_of super := by decide)
    (hmember : {sub, super} ≤ chains := by decide)
  : Beatable (chains.erase ⟦sub⟧) items

axiom Rule1_3 (super left right : Chain)
    (h : Beatable (super ::ₘ chains) items)
    (hvalid : left.last = right.head := by decide)
    (hconcat : super = left.concat right hvalid := by decide)
  : Beatable (⟦left⟧ ::ₘ ⟦right⟧ ::ₘ chains) items

theorem Prop1_2 : Beatable {2 ~~ 1 ~~ 0 ~~ ω ~~ 3} := by
  chain
    Axiom1 (0 ~~ ω)
    Rule1_1 (2 ~~ 1 ~~ 0 ~~ ω ~~ 3)
    Rule1_2 (0 ~~ ω) (2 ~~ 1 ~~ 0 ~~ ω ~~ 3)

theorem Prop1_3 : Beatable {0 ~~ 1 ~~ 2, 1 ~~ 2 ~~ ω} := by
  chain
    Axiom1 (0 ~~ 1 ~~ 2 ~~ ω)
    Rule1_3 (0 ~~ 1 ~~ 2 ~~ ω) (0 ~~ 1) (1 ~~ 2 ~~ ω)
    Rule1_1 (0 ~~ 1 ~~ 2)
    Rule1_2 (0 ~~ 1) (0 ~~ 1 ~~ 2)
