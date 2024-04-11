import Lforge

-- opaque S : Type
-- @[instance] axiom fintype_s : Fintype S

-- instance [f: Fintype α] : CoeDep Type (α : Type) (α → Prop) where
--   coe := (f.elems : Set α)



-- opaque s : Set S

-- #synth Fintype S


sig S {
  a: one Int
}

-- instance [f: Fintype S] : Coe (S : Type) (Finset S) where
--   coe := λ _ ↦ f.elems

-- @[instance] axiom inhabited_s : Inhabited S
-- @[instance] axiom finset_s : Fintype S

-- #synth CoeDep Type S (Finset S)
-- #check (S : Finset S)

-- #check Finset.sum S (fun _ ↦ 0)
-- #check Finset.sum (S : Finset S) (fun _ ↦ 0)
-- #check @Finset.sum ℤ S Int.instAddCommMonoidInt S (fun _ ↦ 0)

-- #lang forge
-- fun test[]: Int {
--   sum x : S | {
--     0
--   }
-- }

-- #check (S : Finset S)
-- #reduce (S : Finset S)

-- def summation {α : Type} (s : Finset α) : Int := Finset.sum s (fun _ => 0)

-- noncomputable opaque n1 : S
-- noncomputable opaque n2 : S

-- def set_s := ({n1, n2} : Set S)

-- #check (S : Finset S)

-- #check Set.ncard

-- #synth AddCommMonoid ℤ

-- #check @Finset.sum ℤ S Int.instAddCommMonoidInt S (fun _ => 0)

-- #synth CoeDep Type S (Finset S)

-- noncomputable instance : Coe S (Finset S) where
--   coe := λ _ ↦ finset_s.elems

-- #check Finset.sum S (fun _ => 1)

-- structure Adder where
--   howMuch : Nat

-- def add5 : Adder := ⟨5⟩

-- instance : CoeFun Adder (fun _ => Nat → Nat) where
--   coe a := (· + a.howMuch)

-- noncomputable instance : Coe Adder ℕ where
--   coe _ := 0

-- #check add5 add5

-- sig Node { edges: set Node }
-- pred graph {
-- some Node
-- all a: Node | some b: Node | b in a.edges
-- edges = ~edges
-- no iden & edges
-- }
-- fun e[x: Node, y: Node] : Node -> Node { x->y + y->x }
-- pred triangle[a: Node, b: Node, c: Node] {
-- e[a, b] + e[a, c] + e[b, c] in edges
-- }
-- pred mesh {
-- graph
-- all a, b: Node | e[a, b] in edges => {
-- one c: Node | triangle[a, b, c]
-- }
-- all a: Node | let B = a.edges | {
-- ^(e[B, B] & edges) = e[B, B]
-- }
-- }
