class strict_partial_order (A : Type u) [LT A] where
  irrefl : ∀ a : A, ¬ a < a
  trans : ∀ a b c : A, a < b → b < c → a < c

open strict_partial_order

variable (A : Type u) [LT A] [strict_partial_order A]

theorem lt_neq (a b : A) (h_lt : a < b) : a ≠ b := by
  intro h_eq
  cases h_eq
  exact irrefl a h_lt

instance : LE A where
  le a b := a < b ∨ a = b

class partial_order where
  refl : ∀ a : A, a ≤ a
  trans : ∀ a b c : A, a ≤ b → b ≤ c → a ≤ c
  antisymm : ∀ a b : A, a ≤ b → b ≤ a → a = b

instance : partial_order A where
  refl a := by
    exact Or.inr rfl

  trans a b c h0 h1 := by
    cases h0 with
    | inl h0_lt =>
      cases h1 with
      | inl h1_lt =>
        have h_lt : a < c := trans a b c h0_lt h1_lt
        exact Or.inl h_lt
      | inr h1_eq =>
        cases h1_eq
        exact Or.inl h0_lt
    | inr h0_eq =>
      cases h0_eq
      exact h1

  antisymm a b h0 h1 := by
    cases h0 with
    | inl h0_lt =>
      cases h1 with
      | inl h1_lt =>
        have h_lt_a : a < a := trans a b a h0_lt h1_lt
        exact False.elim (irrefl a h_lt_a)
      | inr h1_eq =>
        exact h1_eq.symm
    | inr h0_eq =>
      exact h0_eq

open partial_order

theorem lt_of_le_of_lt_thm (a b c : A) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  cases h1 with
  | inl hlt => exact trans a b c hlt h2
  | inr heq => rw [heq]; exact h2

theorem lt_of_lt_of_le_thm (a b c : A) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  cases h2 with
  | inl hlt => exact trans a b c h1 hlt
  | inr heq => rw [<- heq]; exact h1

class strict_linear_order extends strict_partial_order A where
  total : ∀ a b : A, a < b ∨ b < a ∨ a = b

open strict_linear_order

variable (A : Type u) [LT A] [strict_linear_order A]

instance : LE A where
  le a b := a < b ∨ a = b

class linear_order extends partial_order A where
  total : ∀ a b : A, a ≤ b ∨ b ≤ a

instance : linear_order A where
  total a b := by
    have h_tot := total a b
    cases h_tot with
    | inl h_lt_ab =>
      exact Or.inl (Or.inl h_lt_ab)
    | inr h_or =>
      cases h_or with
      | inl h_lt_ba =>
        exact Or.inr (Or.inl h_lt_ba)
      | inr h_eq =>
        exact Or.inl (Or.inr h_eq)


inductive T where
| Z : T
| P : Nat → T → T → T
deriving DecidableEq, Inhabited

open T

def T.fmtJoin : List Std.Format → Std.Format
  | []      => f!""
  | [x]     => x
  | x :: xs => f!"{x} + {T.fmtJoin xs}"

def T.fmtChain : T → List Std.Format
  | Z => []
  | P n t0 t1 =>
    let head :=
      match T.fmtChain t0 with
      | []  => f!"{n}"
      | [e] => f!"{n}^{e}"
      | es  => f!"{n}^({T.fmtJoin es})"
    head :: T.fmtChain t1

def T.fmt (t : T) : Std.Format :=
  match T.fmtChain t with
  | [] => "Z"
  | xs => T.fmtJoin xs

instance : Repr T where
  reprPrec t _ := T.fmt t

structure BIter where
  b : ByteArray
  i : Nat

def mkBIter (s : String) : BIter := { b := s.toUTF8, i := 0 }

def BIter.hasNext (it : BIter) : Bool := it.i < it.b.size

def BIter.curr (it : BIter) : UInt8 := it.b.get! it.i

def BIter.next (it : BIter) : BIter := { it with i := it.i + 1 }

def Parser (α : Type) := BIter → Option (α × BIter)

instance : Monad Parser where
  pure a := fun it => some (a, it)
  bind p f := fun it =>
    match p it with
    | none => none
    | some (a, it') => f a it'

instance : OrElse (Parser α) where
  orElse p q := fun it =>
    match p it with
    | some r => some r
    | none => q () it

def Parser.fail : Parser α := fun _ => none

def peekCh : Parser (Option UInt8) := fun it =>
  some ((if it.hasNext then some it.curr else none), it)

def pchar (c : Char) : Parser Unit := fun it =>
  if it.hasNext ∧ it.curr = c.toNat.toUInt8 then some ((), it.next) else none

def isDigitByte (b : UInt8) : Bool :=
  (48 : UInt8) ≤ b ∧ b ≤ (57 : UInt8)

def pdigit : Parser UInt8 := fun it =>
  if it.hasNext ∧ isDigitByte it.curr then some (it.curr, it.next) else none

def pmanyChar (fuel : Nat) (p : Parser UInt8) : Parser (List UInt8) :=
  match fuel with
  | 0 => fun it => some ([], it)
  | n + 1 =>
    fun it =>
      match p it with
      | none => some ([], it)
      | some (c, it') =>
        match pmanyChar n p it' with
        | some (cs, it'') => some (c :: cs, it'')
        | none => some ([c], it')
termination_by fuel

def pws (fuel : Nat) : Parser Unit :=
  match fuel with
  | 0 => fun it => some ((), it)
  | n + 1 =>
    fun it =>
      if it.hasNext ∧ it.curr = (32 : UInt8) then pws n it.next else some ((), it)
termination_by fuel

def pnat (fuel : Nat) : Parser Nat := do
  let cs ← pmanyChar fuel pdigit
  if cs.isEmpty then Parser.fail
  else pure (cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)

def pZ : Parser T := do
  pchar 'Z'
  pure T.Z

mutual
def pmonomial (fuel : Nat) : Parser (Nat × T) :=
  match fuel with
  | 0 => Parser.fail
  | k + 1 => do
    let nn ← pnat (k + 1)
    pws (k + 1)
    match ← peekCh with
    | some c =>
      if c = ('^'.toNat.toUInt8) then do
        pchar '^'
        pws (k + 1)
        let e ← pexponent k
        pure (nn, e)
      else
        pure (nn, T.Z)
    | none => pure (nn, T.Z)
termination_by fuel

def pexponent (fuel : Nat) : Parser T :=
  match fuel with
  | 0 => Parser.fail
  | k + 1 => do
    match ← peekCh with
    | some c =>
      if c = ('('.toNat.toUInt8) then do
        pchar '('
        pws (k + 1)
        let ms ← pchainList k
        pws (k + 1)
        pchar ')'
        pure (ms.foldr (fun (n, t0) acc => T.P n t0 acc) T.Z)
      else do
        let (n, t0) ← pmonomial k
        pure (T.P n t0 T.Z)
    | none => do
        let (n, t0) ← pmonomial k
        pure (T.P n t0 T.Z)
termination_by fuel

def pchainList (fuel : Nat) : Parser (List (Nat × T)) :=
  match fuel with
  | 0 => Parser.fail
  | k + 1 => do
    let m ← pmonomial k
    pws (k + 1)
    let rest ← pchainListRest k
    pure (m :: rest)
termination_by fuel

def pchainListRest (fuel : Nat) : Parser (List (Nat × T)) :=
  match fuel with
  | 0 => pure []
  | k + 1 =>
    (do
      pchar '+'
      pws (k + 1)
      let m ← pmonomial k
      pws (k + 1)
      let rest ← pchainListRest k
      pure (m :: rest))
    <|> pure []
termination_by fuel
end

def initFuel (s : String) : Nat := 8 * s.toUTF8.size + 64

def pTop (fuel : Nat) : Parser T :=
  pZ <|> (do
    let ms ← pchainList fuel
    pure (ms.foldr (fun (n, t0) acc => T.P n t0 acc) T.Z))

def parseT (s : String) : Option T := do
  let fuel := initFuel s
  let it0 := mkBIter s
  let (_, it1) ← pws fuel it0
  let (t, it2) ← pTop fuel it1
  let (_, it3) ← pws fuel it2
  if it3.hasNext then none else some t

def T.parse! (s : String) : T :=
  match parseT s with
  | some t => t
  | none   => panic! s!"T.parse!: failed to parse \"{s}\""

#eval T.parse! "2^3 + 1"

def T.add : T → T → T
| Z, t => t
| s, Z => s
| P s0 s1 s2, t =>
  P s0 s1 (s2.add t)

def toT : Nat → T
| 0 => Z
| n + 1 => add (toT n) (P 0 Z Z)

instance : Add T where
  add := T.add

instance {n : Nat} : OfNat T n where
  ofNat := toT n

inductive T.Lt : T → T → Prop where
| Z_lt_P (n : Nat) (t1 t2 : T) :
  Z.Lt (P n t1 t2)
| p_head (s0 t0 : Nat) (s1 t1 s2 t2 : T) (h : s0 < t0) :
  (P s0 s1 s2).Lt (P t0 t1 t2)
| p_mid (s0 : Nat) (s1 t1 : T) (s2 t2 : T) (h : T.Lt s1 t1) :
  (P s0 s1 s2).Lt (P s0 t1 t2)
| p_tail (s0 : Nat) (s1 : T) (s2 t2 : T) (h : T.Lt s2 t2) :
  (P s0 s1 s2).Lt (P s0 s1 t2)

instance : LT T where
  lt a b := a.Lt b

theorem lt_Z_Z_inv (h : Z < Z) : False := by
  cases h

theorem lt_P_Z_inv (s0 : Nat) (s1 s2 : T) (h : (P s0 s1 s2) < Z) : False := by
  cases h

theorem lt_Z_inv {a : T} (h : a < Z) : False := by
  cases a with
  | Z => exact lt_Z_Z_inv h
  | P a0 a1 a2 => exact lt_P_Z_inv a0 a1 a2 h

theorem lt_inv (s0 : Nat) (s1 s2 : T) (t0 : Nat) (t1 t2 : T) (h : (P s0 s1 s2).Lt (P t0 t1 t2)) :
  s0 < t0 ∨ (s0 = t0 ∧ s1.Lt t1) ∨ (s0 = t0 ∧ s1 = t1 ∧ s2.Lt t2) := by
  cases h
  case p_head h_lt =>
    apply Or.inl
    exact h_lt
  case p_mid h_lt =>
    apply Or.inr
    apply Or.inl
    apply And.intro
    · rfl
    · exact h_lt
  case p_tail h_lt =>
    apply Or.inr
    apply Or.inr
    apply And.intro
    · rfl
    · apply And.intro
      · rfl
      · exact h_lt

def T.decLt (a b : T) : Decidable (a.Lt b) :=
  match a, b with
  | Z, Z => isFalse lt_Z_Z_inv
  | Z, P n t1 t2 => isTrue (T.Lt.Z_lt_P n t1 t2)
  | P s0 s1 s2, Z => isFalse (lt_P_Z_inv s0 s1 s2)
  | P s0 s1 s2, P t0 t1 t2 =>
    if h0 : s0 < t0 then
      isTrue (T.Lt.p_head s0 t0 s1 t1 s2 t2 h0)
    else
      if heq0 : s0 = t0 then
        match t0, heq0 with
        | _, rfl =>
          match T.decLt s1 t1 with
          | isTrue h1 => isTrue (T.Lt.p_mid s0 s1 t1 s2 t2 h1)
          | isFalse hn1 =>
            if heq1 : s1 = t1 then
              match t1, heq1 with
              | _, rfl =>
                match T.decLt s2 t2 with
                | isTrue h2 => isTrue (T.Lt.p_tail s0 s1 s2 t2 h2)
                | isFalse hn2 =>
                  isFalse (fun h =>
                    match lt_inv s0 s1 s2 s0 s1 t2 h with
                    | Or.inl h_lt => h0 h_lt
                    | Or.inr (Or.inl h_and) => hn1 h_and.2
                    | Or.inr (Or.inr h_and) => hn2 h_and.2.2
                  )
            else
              isFalse (fun h =>
                match lt_inv s0 s1 s2 s0 t1 t2 h with
                | Or.inl h_lt => h0 h_lt
                | Or.inr (Or.inl h_and) => hn1 h_and.2
                | Or.inr (Or.inr h_and) => heq1 h_and.2.1
              )
      else
        isFalse (fun h =>
          match lt_inv s0 s1 s2 t0 t1 t2 h with
          | Or.inl h_lt => h0 h_lt
          | Or.inr (Or.inl h_and) => heq0 h_and.1
          | Or.inr (Or.inr h_and) => heq0 h_and.1
        )

instance (a b : T) : Decidable (a < b) :=
  T.decLt a b

theorem nat_lt_total (n m : Nat) : n < m ∨ m < n ∨ n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      apply Or.inr
      apply Or.inr
      rfl
    | succ m' =>
      apply Or.inl
      apply Nat.zero_lt_succ
  | succ n' ih =>
    cases m with
    | zero =>
      apply Or.inr
      apply Or.inl
      apply Nat.zero_lt_succ
    | succ m' =>
      cases ih m' with
      | inl h_lt =>
        apply Or.inl
        exact Nat.succ_lt_succ h_lt
      | inr h_or =>
        cases h_or with
        | inl h_gt =>
          apply Or.inr
          apply Or.inl
          exact Nat.succ_lt_succ h_gt
        | inr h_eq =>
          apply Or.inr
          apply Or.inr
          rw [h_eq]

theorem lt_irrefl_thm (a : T) : ¬ a.Lt a := by
  induction a with
  | Z =>
    intro h
    exact lt_Z_Z_inv h
  | P s0 s1 s2 ih1 ih2 =>
    intro h
    have h_inv := lt_inv s0 s1 s2 s0 s1 s2 h
    cases h_inv with
    | inl h_lt =>
      exact Nat.lt_irrefl s0 h_lt
    | inr h_or =>
      cases h_or with
      | inl h_and =>
        exact ih1 h_and.2
      | inr h_and =>
        exact ih2 h_and.2.2

theorem lt_trans_thm (a : T) : ∀ b c : T, a.Lt b → b.Lt c → a.Lt c := by
  induction a with
  | Z =>
    intro b c h1 h2
    cases b with
    | Z => exact False.elim (lt_Z_Z_inv h1)
    | P b0 b1 b2 =>
      cases c with
      | Z => exact False.elim (lt_P_Z_inv b0 b1 b2 h2)
      | P c0 c1 c2 => exact T.Lt.Z_lt_P c0 c1 c2
  | P a0 a1 a2 ih1 ih2 =>
    intro b c h1 h2
    cases b with
    | Z => exact False.elim (lt_P_Z_inv a0 a1 a2 h1)
    | P b0 b1 b2 =>
      cases c with
      | Z => exact False.elim (lt_P_Z_inv b0 b1 b2 h2)
      | P c0 c1 c2 =>
        have h1_inv := lt_inv a0 a1 a2 b0 b1 b2 h1
        have h2_inv := lt_inv b0 b1 b2 c0 c1 c2 h2
        cases h1_inv with
        | inl h1_head =>
          cases h2_inv with
          | inl h2_head =>
            have h_trans := Nat.lt_trans h1_head h2_head
            exact T.Lt.p_head a0 c0 a1 c1 a2 c2 h_trans
          | inr h2_or =>
            cases h2_or with
            | inl h2_mid =>
              cases h2_mid.1
              exact T.Lt.p_head a0 b0 a1 c1 a2 c2 h1_head
            | inr h2_tail =>
              cases h2_tail.1
              exact T.Lt.p_head a0 b0 a1 c1 a2 c2 h1_head
        | inr h1_or =>
          cases h1_or with
          | inl h1_mid =>
            cases h1_mid.1
            cases h2_inv with
            | inl h2_head =>
              exact T.Lt.p_head a0 c0 a1 c1 a2 c2 h2_head
            | inr h2_or =>
              cases h2_or with
              | inl h2_mid =>
                cases h2_mid.1
                have h_trans := ih1 b1 c1 h1_mid.2 h2_mid.2
                exact T.Lt.p_mid a0 a1 c1 a2 c2 h_trans
              | inr h2_tail =>
                cases h2_tail.1
                cases h2_tail.2.1
                exact T.Lt.p_mid a0 a1 b1 a2 c2 h1_mid.2
          | inr h1_tail =>
            cases h1_tail.1
            cases h1_tail.2.1
            cases h2_inv with
            | inl h2_head =>
              exact T.Lt.p_head a0 c0 a1 c1 a2 c2 h2_head
            | inr h2_or =>
              cases h2_or with
              | inl h2_mid =>
                cases h2_mid.1
                exact T.Lt.p_mid a0 a1 c1 a2 c2 h2_mid.2
              | inr h2_tail =>
                cases h2_tail.1
                cases h2_tail.2.1
                have h_trans := ih2 b2 c2 h1_tail.2.2 h2_tail.2.2
                exact T.Lt.p_tail a0 a1 a2 c2 h_trans

theorem lt_asymm_thm {a b : T} (h : a < b) : ¬ (b < a) := by
  intro hba
  have htrans := lt_trans_thm a b a h hba
  exact lt_irrefl_thm a htrans

theorem lt_total_thm (a b : T) : a.Lt b ∨ b.Lt a ∨ a = b := by
  induction a generalizing b with
  | Z =>
    cases b with
    | Z =>
      apply Or.inr
      apply Or.inr
      rfl
    | P b0 b1 b2 =>
      apply Or.inl
      exact T.Lt.Z_lt_P b0 b1 b2
  | P a0 a1 a2 ih1 ih2 =>
    cases b with
    | Z =>
      apply Or.inr
      apply Or.inl
      exact T.Lt.Z_lt_P a0 a1 a2
    | P b0 b1 b2 =>
      cases nat_lt_total a0 b0 with
      | inl h_lt =>
        apply Or.inl
        exact T.Lt.p_head a0 b0 a1 b1 a2 b2 h_lt
      | inr h_or =>
        cases h_or with
        | inl h_gt =>
          apply Or.inr
          apply Or.inl
          exact T.Lt.p_head b0 a0 b1 a1 b2 a2 h_gt
        | inr h_eq =>
          cases h_eq
          cases ih1 b1 with
          | inl h1_lt =>
            apply Or.inl
            exact T.Lt.p_mid a0 a1 b1 a2 b2 h1_lt
          | inr h1_or =>
            cases h1_or with
            | inl h1_gt =>
              apply Or.inr
              apply Or.inl
              exact T.Lt.p_mid a0 b1 a1 b2 a2 h1_gt
            | inr h1_eq =>
              cases h1_eq
              cases ih2 b2 with
              | inl h2_lt =>
                apply Or.inl
                exact T.Lt.p_tail a0 a1 a2 b2 h2_lt
              | inr h2_or =>
                cases h2_or with
                | inl h2_gt =>
                  apply Or.inr
                  apply Or.inl
                  exact T.Lt.p_tail a0 a1 b2 a2 h2_gt
                | inr h2_eq =>
                  cases h2_eq
                  apply Or.inr
                  apply Or.inr
                  rfl

instance : strict_partial_order T where
  irrefl a := lt_irrefl_thm a
  trans a b c hf hs := lt_trans_thm a b c hf hs

instance : strict_linear_order T where
  total a b := lt_total_thm a b

instance (a b : T) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

theorem Z_le (s : T) : Z ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P s0 s1 s2 =>
    apply Or.inl
    exact T.Lt.Z_lt_P s0 s1 s2

def T.size : T → Nat
| Z => 0
| P _ t1 t2 => t1.size + t2.size + 1

inductive T.index_Prop : T → T → Prop where
| Z_holds (t : T) : T.index_Prop Z t
| P_holds (s0 : Nat) (s1 s2 t : T) (h : P s0 s1 Z < t) (hrec : T.index_Prop s2 t) :
  T.index_Prop (P s0 s1 s2) t

theorem index_Prop_inv (s0 : Nat) (s1 s2 t : T) (h : T.index_Prop (P s0 s1 s2) t) :
  P s0 s1 Z < t ∧ T.index_Prop s2 t := by
  cases h with
  | P_holds _ _ _ _ hlt hrec =>
    exact ⟨hlt, hrec⟩

theorem index_Prop_Z_iff (t : T) : T.index_Prop Z t ↔ True := by
  apply Iff.intro
  · intro _
    exact True.intro
  · intro _
    exact T.index_Prop.Z_holds t

theorem index_Prop_P_iff (s0 : Nat) (s1 s2 t : T) :
  T.index_Prop (P s0 s1 s2) t ↔ (if P s0 s1 Z < t then T.index_Prop s2 t else False) := by
  apply Iff.intro
  · intro h
    have hp := index_Prop_inv s0 s1 s2 t h
    rw [if_pos hp.1]
    exact hp.2
  · intro h
    cases hdec : (inferInstance : Decidable (P s0 s1 Z < t)) with
    | isTrue hlt =>
      rw [if_pos hlt] at h
      exact T.index_Prop.P_holds s0 s1 s2 t hlt h
    | isFalse hnlt =>
      rw [if_neg hnlt] at h
      exact False.elim h

def T.indexPropDecidable : (s t : T) → Decidable (T.index_Prop s t)
| Z, t => isTrue (T.index_Prop.Z_holds t)
| P s0 s1 s2, t =>
  if h : P s0 s1 Z < t then
    match T.indexPropDecidable s2 t with
    | isTrue hp => isTrue (T.index_Prop.P_holds s0 s1 s2 t h hp)
    | isFalse hn => isFalse (fun hcontra => hn (index_Prop_inv s0 s1 s2 t hcontra).2)
  else
    isFalse (fun hcontra => h (index_Prop_inv s0 s1 s2 t hcontra).1)

instance (s t : T) : Decidable (T.index_Prop s t) := T.indexPropDecidable s t

inductive Dom2 where
| Zero
| One
| ω
| M (s : Nat)
| Ω (l s0 : Nat) (s1 : T)
deriving DecidableEq

def T.dom2 : T → Dom2
| Z => .Zero
| P s0 s1 Z =>
  match dom2 s1 with
  | .Zero =>
    match s0 with
    | 0 => .One
    | _ + 1 => .M s0
  | .One => .ω
  | .ω => .ω
  | .M l =>
    if s0 < l then
      if s0 + 1 < l then
        .ω
      else .Ω l s0 s1
    else .M l
  | .Ω l l0 l1 =>
    if P s0 s1 Z < P l0 l1 Z then
      .ω
    else .Ω l l0 l1
| P _ _ s2 =>
  dom2 s2

def T.mul : T → T → T
| _, Z => Z
| a, P _ _ m2 => mul a m2 + a

def T.iter1 (s0 : Nat) (F : T → T) : T → T
| Z => Z
| P _ _ m2 =>
  let prev := iter1 s0 F m2
  P s0 (F prev) Z

def T.iter2 (li : Nat) (F1 F2 : T → T) : T → T
| Z => Z
| P _ _ m2 =>
  let prev := iter2 li F1 F2 m2
  P li (F1 (F2 prev)) Z

def T.drop (s t : T) : T :=
  match s with
  | Z => Z
  | P _ s1 s2 =>
    if T.index_Prop s t then s
    else match s2 with
      | Z => drop s1 t
      | P _ _ _ => drop s2 t

theorem T.size_P (s0 : Nat) (s1 s2 : T) : (P s0 s1 s2).size = s1.size + s2.size + 1 := rfl

theorem T.drop_size_le : ∀ (s t : T), (T.drop s t).size ≤ s.size := by
  intro s
  induction s with
  | Z =>
    intro t
    simp [T.drop]
  | P s0 s1 s2 ih1 ih2 =>
    intro t
    simp only [T.drop]
    split
    · omega
    · cases s2 with
      | Z =>
        have h1 := ih1 t
        simp [T.size] at h1 ⊢
        omega
      | P s20 s21 s22 =>
        have h2 := ih2 t
        simp [T.size] at h2 ⊢
        omega

theorem T.dom2_Ω_size_lt : ∀ (s : T) (l l0 : Nat) (l1 : T),
    T.dom2 s = .Ω l l0 l1 → l1.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 h
    simp [T.dom2] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 h
    cases s2 with
    | Z =>
      simp only [T.dom2] at h
      cases hd1 : T.dom2 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
            obtain ⟨e1, e2, e3⟩ := h
            subst e1; subst e2; subst e3
            simp [T.size]
        · simp [hc1] at h
      | Ω l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc] at h
          · simp [hc] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3⟩ := h
          subst e1; subst e2; subst e3
          have hlt := ih1 l' l0' l1' hd1
          simp [T.size_P]
          omega
    | P s20 s21 s22 =>
      simp only [T.dom2] at h
      have hlt := ih2 l l0 l1 h
      simp only [T.size_P] at hlt ⊢
      omega

inductive T.IsN : T → Prop
| zero : T.IsN Z
| succ : ∀ t : T, T.IsN t → T.IsN (P 0 Z t)

def T.ValidArg2 (s t : T) : Prop :=
  match dom2 s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t
  | .M l => T.index_Prop t (P l Z Z)
  | .Ω _ l0 l1 => T.index_Prop t (P l0 l1 Z)

def T.fund2 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 Z =>
    match _h1 : T.dom2 s1 with
    | .Zero => t
    | .One => T.mul (P s0 (T.fund2 s1 Z) Z) t
    | .ω => P s0 (T.fund2 s1 t) Z
    | .M l =>
      if s0 < l then
        if s0 + 1 < l then
          let F := fun x => T.fund2 s1 x
          P s0 (T.fund2 s1 (T.iter1 s0 F t)) Z
        else t
      else P s0 (T.fund2 s1 t) Z
    | .Ω l l0 l1 =>
      if P s0 s1 Z < P l0 l1 Z then
        if s0 + 1 < l then
          let F1 := fun x => T.fund2 l1 x
          let F2 := fun x => P l0 (T.fund2 s1 x) Z
          P s0 (T.fund2 s1 (T.iter2 l0 F1 F2 t)) Z
        else
          let F1 := fun x => T.fund2 l1 x
          let F2 := fun x => T.fund2 (T.drop s1 (P l Z Z)) x
          P s0 (T.fund2 s1 (T.iter2 l0 F1 F2 t)) Z
      else P s0 (T.fund2 s1 t) Z
  | P s0 s1 (P s20 s21 s22) =>
    P s0 s1 (T.fund2 (P s20 s21 s22) t)
termination_by s.size
decreasing_by
  all_goals (
    simp only [T.size]
    first
      | omega
      | (have hΩ := T.dom2_Ω_size_lt _ _ _ _ _h1; omega)
      | (have hD := T.drop_size_le s1 (P l Z Z); omega)
  )

#eval! fund2 (parse! "0^0^2^1^2") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^(2^1^2 + 2^1^2)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^2^(1^2 + 1^2)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^2^1^(2 + 2)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^(0^1 + 0^1)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^(1 + 1)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^(1^0^1 + 1^0^1)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^(0^1^0^1 + 0^1^0^1)") (parse! "0 + 0 + 0")

def T.takeAt (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 Z =>
    if s = t then Z
    else P s0 (s1.takeAt t) Z
  | P s0 s1 s2 => P s0 s1 (s2.takeAt t)

inductive Dom3 where
| Zero
| One
| ω
| M2 (s : Nat)
| M1 (l s0 : Nat) (s1 : T)
| Ω (l s0 : Nat) (s1 s2 : T)
deriving DecidableEq

def T.dom3 : T → Dom3
| Z => .Zero
| P s0 s1 Z =>
  match T.dom3 s1 with
  | .Zero =>
    match s0 with
    | 0 => .One
    | _ + 1 => .M2 s0
  | .One => .ω
  | .ω => .ω
  | .M2 l =>
    if s0 < l then
      if s0 + 1 < l then
        .ω
      else .M1 l s0 s1
    else .M2 l
  | .M1 l l0 l1 =>
    if P s0 s1 Z < P l0 l1 Z then
      if s0 + 1 < l then
        .ω
      else
        if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
          .ω
        else .Ω l l0 l1 s1
    else .M1 l l0 l1
  | .Ω l l0 l1 l2 =>
    if P s0 s1 Z < P l0 l2 Z then
      .ω
    else .Ω l l0 l1 l2
| P _ _ s2 =>
  T.dom3 s2

theorem T.dom3_M1_size_lt : ∀ (s : T) (l l0 : Nat) (l1 : T),
    T.dom3 s = .M1 l l0 l1 → l1.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 h
    simp [T.dom3] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 h
    cases s2 with
    | Z =>
      simp only [T.dom3] at h
      cases hd1 : T.dom3 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M2 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
            obtain ⟨e1, e2, e3⟩ := h
            subst e1; subst e2; subst e3
            simp [T.size]
        · simp [hc1] at h
      | M1 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3⟩ := h
          subst e1; subst e2; subst e3
          have hlt := ih1 l' l0' l1' hd1
          simp [T.size_P]
          omega
      | Ω l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc] at h
            · simp [hc] at h
        · simp [hc] at h
    | P s20 s21 s22 =>
      simp only [T.dom3] at h
      have hlt := ih2 l l0 l1 h
      simp only [T.size_P] at hlt ⊢
      omega

theorem T.dom3_Ω_l1_size_lt : ∀ (s : T) (l l0 : Nat) (l1 l2 : T),
    T.dom3 s = .Ω l l0 l1 l2 → l1.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 l2 h
    simp [T.dom3] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 l2 h
    cases s2 with
    | Z =>
      simp only [T.dom3] at h
      cases hd1 : T.dom3 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M2 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
        · simp [hc1] at h
      | M1 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
              obtain ⟨e1, e2, e3, e4⟩ := h
              subst e1; subst e2; subst e3; subst e4
              have hM1 := T.dom3_M1_size_lt s1 l' l0' l1' hd1
              simp [T.size]
              omega
        · simp [hc] at h
      | Ω l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc] at h
            · simp [hc] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3, e4⟩ := h
          subst e1; subst e2; subst e3; subst e4
          have hlt := ih1 l' l0' l1' l2' hd1
          simp [T.size_P]
          omega
    | P s20 s21 s22 =>
      simp only [T.dom3] at h
      have hlt := ih2 l l0 l1 l2 h
      simp only [T.size_P] at hlt ⊢
      omega

theorem T.dom3_Ω_l3_size_lt : ∀ (s : T) (l l0 : Nat) (l1 l2 : T),
    T.dom3 s = .Ω l l0 l1 l2 → l2.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 l2 h
    simp [T.dom3] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 l2 h
    cases s2 with
    | Z =>
      simp only [T.dom3] at h
      cases hd1 : T.dom3 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M2 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
        · simp [hc1] at h
      | M1 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
              obtain ⟨e1, e2, e3, e4⟩ := h
              subst e1; subst e2; subst e3; subst e4
              simp [T.size]
        · simp [hc] at h
      | Ω l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc] at h
            · simp [hc] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3, e4⟩ := h
          subst e1; subst e2; subst e3; subst e4
          have hlt := ih1 l' l0' l1' l2' hd1
          simp [T.size_P]
          omega
    | P s20 s21 s22 =>
      simp only [T.dom3] at h
      have hlt := ih2 l l0 l1 l2 h
      simp only [T.size_P] at hlt ⊢
      omega

def T.iter3 (li : Nat) (F1 F2 F3 : T → T) : T → T
| Z => Z
| P _ _ m2 =>
  let prev := iter3 li F1 F2 F3 m2
  P li (F1 (F2 (F3 prev))) Z

def T.ValidArg3 (s t : T) : Prop :=
  match dom3 s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t
  | .M2 l => T.index_Prop t (P l Z Z)
  | .M1 _ l0 l1 => T.index_Prop t (P l0 l1 Z)
  | .Ω _ l0 _ l2 => T.index_Prop t (P l0 l2 Z)

def T.fund3 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 Z =>
    match _h1 : T.dom3 s1 with
    | .Zero => t
    | .One => T.mul (P s0 (T.fund3 s1 Z) Z) t
    | .ω => P s0 (T.fund3 s1 t) Z
    | .M2 l =>
      if s0 < l then
        if s0 + 1 < l then
          let F := T.fund3 s1
          P s0 (T.fund3 s1 (T.iter1 s0 F t)) Z
        else t
      else P s0 (T.fund3 s1 t) Z
    | .M1 l l0 l1 =>
      if P s0 s1 Z < P l0 l1 Z then
        if s0 + 1 < l then
          let F1 := T.fund3 l1
          let F2 := fun x => P l0 (T.fund3 s1 x) Z
          P s0 (T.fund3 s1 (T.iter2 l0 F1 F2 t)) Z
        else
          if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
            let F1 := T.fund3 l1
            let F2 := T.fund3 (T.drop s1 (P l Z Z))
            P s0 (T.fund3 s1 (T.iter2 l0 F1 F2 t)) Z
          else t
      else P s0 (T.fund3 s1 t) Z
    | .Ω l l0 l1 l2 =>
      if P s0 s1 Z < P l0 l2 Z then
        if s0 + 1 < l then
          let F1 := T.fund3 l2
          let F2 := fun x => P l0 (T.fund3 l1 x) Z
          let F3 := fun x => P l0 (T.fund3 s1 x) Z
          P s0 (T.fund3 s1 (T.iter3 l0 F1 F2 F3 t)) Z
        else
          if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
            let F1 := T.fund3 l2
            let F2 := fun x => P l0 (T.fund3 l1 x) Z
            let F3 := T.fund3 (T.drop s1 (P l Z Z))
            P s0 (T.fund3 s1 (T.iter3 l0 F1 F2 F3 t)) Z
          else
            let F1 := T.fund3 l2
            let F2 := T.fund3 (T.drop s1 (P l0 l1 Z))
            P s0 (T.fund3 s1 (T.iter2 l0 F1 F2 t)) Z
      else P s0 (T.fund3 s1 t) Z
  | P s0 s1 (P s20 s21 s22) =>
    P s0 s1 (T.fund3 (P s20 s21 s22) t)
termination_by s.size
decreasing_by
  all_goals (
    simp only [T.size]
    first
      | omega
      | (have hM1 := T.dom3_M1_size_lt _ _ _ _ _h1; omega)
      | (have hΩ1 := T.dom3_Ω_l1_size_lt _ _ _ _ _ _h1; omega)
      | (have hΩ3 := T.dom3_Ω_l3_size_lt _ _ _ _ _ _h1; omega)
      | (have hD := T.drop_size_le s1 (P l Z Z); omega)
      | (have hD := T.drop_size_le s1 (P l0 l1 Z); omega)
  )

#eval fund3 (parse! "0^0^0^2^2^1^1^2^1^2") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^(1 + 1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^(0^(1 + 1) + 0^(1 + 1))") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^1^1^0^1^0^1^1") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^1^1^0^1^0^1^(1 + 1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^1^1^0^1^0^(1^1 + 1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^1^1^0^1^(0^1^1 + 0^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^1^1^0^(1^0^1^1 + 1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^1^1^(0^1^0^1^1 + 0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^1^(1^0^1^0^1^1 + 1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^0^(1^1^0^1^0^1^1 + 1^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^(0^0^1 + 0^0^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^0^(0^1 + 0^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^(0^(0^1+0^1)+0^(0^1+0^1))") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^0^1^1^0^1^1^1") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^0^1^1^0^1^1^(1+1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^0^1^1^0^1^(1^1+1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^0^1^1^0^(1^1^1+1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^0^1^1^(0^1^1^1+0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^0^1^(1^0^1^1^1+1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^0^(1^1^0^1^1^1+1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^1^(0^1^1^0^1^1^1+0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^1^(1^0^1^1^0^1^1^1+1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^1^(1^1^0^1^1^0^1^1^1+1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^0^(1^1^1^0^1^1^0^1^1^1+1^1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^1^(0^1^1^1^0^1^1^0^1^1^1+0^1^1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval fund3 (parse! "0^(1^0^1^1^1^0^1^1^0^1^1^1+1^0^1^1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

inductive Dom4 where
| Zero
| One
| ω
| M3 (s : Nat)
| M2 (l s0 : Nat) (s1 : T)
| M1 (l s0 : Nat) (s1 s2 : T)
| Ω (l s0 : Nat) (s1 s2 s3 : T)
deriving DecidableEq

def T.iter4 (li : Nat) (F1 F2 F3 F4 : T → T) : T → T
| Z => Z
| P _ _ m2 =>
  let prev := iter4 li F1 F2 F3 F4 m2
  P li (F1 (F2 (F3 (F4 prev)))) Z

def T.dom4 : T → Dom4
| Z => .Zero
| P s0 s1 Z =>
  match T.dom4 s1 with
  | .Zero =>
    match s0 with
    | 0 => .One
    | _ + 1 => .M3 s0
  | .One => .ω
  | .ω => .ω
  | .M3 l =>
    if s0 < l then
      if s0 + 1 < l then
        .ω
      else .M2 l s0 s1
    else .M3 l
  | .M2 l l0 l1 =>
    if P s0 s1 Z < P l0 l1 Z then
      if s0 + 1 < l then
        .ω
      else
        if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
          .ω
        else .M1 l l0 l1 s1
    else .M2 l l0 l1
  | .M1 l l0 l1 l2 =>
    if P s0 s1 Z < P l0 l2 Z then
      if s0 + 1 < l then
        .ω
      else
        if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
          .ω
        else
          if P s0 s1 Z < (P l0 l2 Z).takeAt (P l0 l1 Z) then
            .ω
          else .Ω l l0 l1 l2 s1
    else .M1 l l0 l1 l2
  | .Ω l l0 l1 l2 l3 =>
    if P s0 s1 Z < P l0 l3 Z then
      .ω
    else .Ω l l0 l1 l2 l3
| P _ _ s2 =>
  T.dom4 s2

theorem T.dom4_M2_size_lt : ∀ (s : T) (l l0 : Nat) (l1 : T),
    T.dom4 s = .M2 l l0 l1 → l1.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 h
    simp [T.dom4] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 h
    cases s2 with
    | Z =>
      simp only [T.dom4] at h
      cases hd1 : T.dom4 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M3 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
            obtain ⟨e1, e2, e3⟩ := h
            subst e1; subst e2; subst e3
            simp [T.size]
        · simp [hc1] at h
      | M2 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3⟩ := h
          subst e1; subst e2; subst e3
          have hlt := ih1 l' l0' l1' hd1
          simp [T.size_P]
          omega
      | M1 l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · by_cases hc4 : P s0 s1 Z < (P l0' l2' Z).takeAt (P l0' l1' Z)
              · simp [hc, hc2, hc3, hc4] at h
              · simp [hc, hc2, hc3, hc4] at h
        · simp [hc] at h
      | Ω l' l0' l1' l2' l3' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l3' Z
        · simp [hc] at h
        · simp [hc] at h
    | P s20 s21 s22 =>
      simp only [T.dom4] at h
      have hlt := ih2 l l0 l1 h
      simp only [T.size_P] at hlt ⊢
      omega

theorem T.dom4_M1_l1_size_lt : ∀ (s : T) (l l0 : Nat) (l1 l2 : T),
    T.dom4 s = .M1 l l0 l1 l2 → l1.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 l2 h
    simp [T.dom4] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 l2 h
    cases s2 with
    | Z =>
      simp only [T.dom4] at h
      cases hd1 : T.dom4 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M3 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
        · simp [hc1] at h
      | M2 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
              obtain ⟨e1, e2, e3, e4⟩ := h
              subst e1; subst e2; subst e3; subst e4
              have hM2 := T.dom4_M2_size_lt s1 l' l0' l1' hd1
              simp [T.size]
              omega
        · simp [hc] at h
      | M1 l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · by_cases hc4 : P s0 s1 Z < (P l0' l2' Z).takeAt (P l0' l1' Z)
              · simp [hc, hc2, hc3, hc4] at h
              · simp [hc, hc2, hc3, hc4] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3, e4⟩ := h
          subst e1; subst e2; subst e3; subst e4
          have hlt := ih1 l' l0' l1' l2' hd1
          simp [T.size_P]
          omega
      | Ω l' l0' l1' l2' l3' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l3' Z
        · simp [hc] at h
        · simp [hc] at h
    | P s20 s21 s22 =>
      simp only [T.dom4] at h
      have hlt := ih2 l l0 l1 l2 h
      simp only [T.size_P] at hlt ⊢
      omega

theorem T.dom4_M1_l2_size_lt : ∀ (s : T) (l l0 : Nat) (l1 l2 : T),
    T.dom4 s = .M1 l l0 l1 l2 → l2.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 l2 h
    simp [T.dom4] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 l2 h
    cases s2 with
    | Z =>
      simp only [T.dom4] at h
      cases hd1 : T.dom4 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M3 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
        · simp [hc1] at h
      | M2 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
              obtain ⟨e1, e2, e3, e4⟩ := h
              subst e1; subst e2; subst e3; subst e4
              simp [T.size]
        · simp [hc] at h
      | M1 l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · by_cases hc4 : P s0 s1 Z < (P l0' l2' Z).takeAt (P l0' l1' Z)
              · simp [hc, hc2, hc3, hc4] at h
              · simp [hc, hc2, hc3, hc4] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3, e4⟩ := h
          subst e1; subst e2; subst e3; subst e4
          have hlt := ih1 l' l0' l1' l2' hd1
          simp [T.size_P]
          omega
      | Ω l' l0' l1' l2' l3' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l3' Z
        · simp [hc] at h
        · simp [hc] at h
    | P s20 s21 s22 =>
      simp only [T.dom4] at h
      have hlt := ih2 l l0 l1 l2 h
      simp only [T.size_P] at hlt ⊢
      omega

theorem T.dom4_Ω_l1_size_lt : ∀ (s : T) (l l0 : Nat) (l1 l2 l3 : T),
    T.dom4 s = .Ω l l0 l1 l2 l3 → l1.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 l2 l3 h
    simp [T.dom4] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 l2 l3 h
    cases s2 with
    | Z =>
      simp only [T.dom4] at h
      cases hd1 : T.dom4 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M3 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
        · simp [hc1] at h
      | M2 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
        · simp [hc] at h
      | M1 l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · by_cases hc4 : P s0 s1 Z < (P l0' l2' Z).takeAt (P l0' l1' Z)
              · simp [hc, hc2, hc3, hc4] at h
              · simp [hc, hc2, hc3, hc4] at h
                obtain ⟨e1, e2, e3, e4, e5⟩ := h
                subst e1; subst e2; subst e3; subst e4; subst e5
                have hM1 := T.dom4_M1_l1_size_lt s1 l' l0' l1' l2' hd1
                simp [T.size]
                omega
        · simp [hc] at h
      | Ω l' l0' l1' l2' l3' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l3' Z
        · simp [hc] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3, e4, e5⟩ := h
          subst e1; subst e2; subst e3; subst e4; subst e5
          have hlt := ih1 l' l0' l1' l2' l3' hd1
          simp [T.size_P]
          omega
    | P s20 s21 s22 =>
      simp only [T.dom4] at h
      have hlt := ih2 l l0 l1 l2 l3 h
      simp only [T.size_P] at hlt ⊢
      omega

theorem T.dom4_Ω_l2_size_lt : ∀ (s : T) (l l0 : Nat) (l1 l2 l3 : T),
    T.dom4 s = .Ω l l0 l1 l2 l3 → l2.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 l2 l3 h
    simp [T.dom4] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 l2 l3 h
    cases s2 with
    | Z =>
      simp only [T.dom4] at h
      cases hd1 : T.dom4 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M3 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
        · simp [hc1] at h
      | M2 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
        · simp [hc] at h
      | M1 l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · by_cases hc4 : P s0 s1 Z < (P l0' l2' Z).takeAt (P l0' l1' Z)
              · simp [hc, hc2, hc3, hc4] at h
              · simp [hc, hc2, hc3, hc4] at h
                obtain ⟨e1, e2, e3, e4, e5⟩ := h
                subst e1; subst e2; subst e3; subst e4; subst e5
                have hM1 := T.dom4_M1_l2_size_lt s1 l' l0' l1' l2' hd1
                simp [T.size]
                omega
        · simp [hc] at h
      | Ω l' l0' l1' l2' l3' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l3' Z
        · simp [hc] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3, e4, e5⟩ := h
          subst e1; subst e2; subst e3; subst e4; subst e5
          have hlt := ih1 l' l0' l1' l2' l3' hd1
          simp [T.size_P]
          omega
    | P s20 s21 s22 =>
      simp only [T.dom4] at h
      have hlt := ih2 l l0 l1 l2 l3 h
      simp only [T.size_P] at hlt ⊢
      omega

theorem T.dom4_Ω_l3_size_lt : ∀ (s : T) (l l0 : Nat) (l1 l2 l3 : T),
    T.dom4 s = .Ω l l0 l1 l2 l3 → l3.size < s.size := by
  intro s
  induction s with
  | Z =>
    intro l l0 l1 l2 l3 h
    simp [T.dom4] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l0 l1 l2 l3 h
    cases s2 with
    | Z =>
      simp only [T.dom4] at h
      cases hd1 : T.dom4 s1 with
      | Zero =>
        rw [hd1] at h
        cases s0 with
        | zero => simp at h
        | succ n => simp at h
      | One =>
        rw [hd1] at h
        simp at h
      | ω =>
        rw [hd1] at h
        simp at h
      | M3 l' =>
        rw [hd1] at h
        by_cases hc1 : s0 < l'
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc1, hc2] at h
          · simp [hc1, hc2] at h
        · simp [hc1] at h
      | M2 l' l0' l1' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l1' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · simp [hc, hc2, hc3] at h
        · simp [hc] at h
      | M1 l' l0' l1' l2' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l2' Z
        · by_cases hc2 : s0 + 1 < l'
          · simp [hc, hc2] at h
          · by_cases hc3 : P s0 s1 Z < (P l0' l1' Z).takeAt (P l' Z Z)
            · simp [hc, hc2, hc3] at h
            · by_cases hc4 : P s0 s1 Z < (P l0' l2' Z).takeAt (P l0' l1' Z)
              · simp [hc, hc2, hc3, hc4] at h
              · simp [hc, hc2, hc3, hc4] at h
                obtain ⟨e1, e2, e3, e4, e5⟩ := h
                subst e1; subst e2; subst e3; subst e4; subst e5
                simp [T.size]
        · simp [hc] at h
      | Ω l' l0' l1' l2' l3' =>
        rw [hd1] at h
        by_cases hc : P s0 s1 Z < P l0' l3' Z
        · simp [hc] at h
        · simp [hc] at h
          obtain ⟨e1, e2, e3, e4, e5⟩ := h
          subst e1; subst e2; subst e3; subst e4; subst e5
          have hlt := ih1 l' l0' l1' l2' l3' hd1
          simp [T.size_P]
          omega
    | P s20 s21 s22 =>
      simp only [T.dom4] at h
      have hlt := ih2 l l0 l1 l2 l3 h
      simp only [T.size_P] at hlt ⊢
      omega

def T.ValidArg4 (s t : T) : Prop :=
  match dom4 s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t
  | .M3 l => T.index_Prop t (P l Z Z)
  | .M2 _ l0 l1 => T.index_Prop t (P l0 l1 Z)
  | .M1 _ l0 _ l2 => T.index_Prop t (P l0 l2 Z)
  | .Ω _ l0 _ _ l3 => T.index_Prop t (P l0 l3 Z)

def T.fund4 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 Z =>
    match _h1 : T.dom4 s1 with
    | .Zero => t
    | .One => T.mul (P s0 (T.fund4 s1 Z) Z) t
    | .ω => P s0 (T.fund4 s1 t) Z
    | .M3 l =>
      if s0 < l then
        if s0 + 1 < l then
          let F := T.fund4 s1
          P s0 (T.fund4 s1 (T.iter1 s0 F t)) Z
        else t
      else P s0 (T.fund4 s1 t) Z
    | .M2 l l0 l1 =>
      if P s0 s1 Z < P l0 l1 Z then
        if s0 + 1 < l then
          let F1 := T.fund4 l1
          let F2 := fun x => P l0 (T.fund4 s1 x) Z
          P s0 (T.fund4 s1 (T.iter2 l0 F1 F2 t)) Z
        else
          if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
            let F1 := T.fund4 l1
            let F2 := T.fund4 (T.drop s1 (P l Z Z))
            P s0 (T.fund4 s1 (T.iter2 l0 F1 F2 t)) Z
          else t
      else P s0 (T.fund4 s1 t) Z
    | .M1 l l0 l1 l2 =>
      if P s0 s1 Z < P l0 l2 Z then
        if s0 + 1 < l then
          let F1 := T.fund4 l2
          let F2 := fun x => P l0 (T.fund4 l1 x) Z
          let F3 := fun x => P l0 (T.fund4 s1 x) Z
          P s0 (T.fund4 s1 (T.iter3 l0 F1 F2 F3 t)) Z
        else
          if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
            let F1 := T.fund4 l2
            let F2 := fun x => P l0 (T.fund4 l1 x) Z
            let F3 := T.fund4 (T.drop s1 (P l Z Z))
            P s0 (T.fund4 s1 (T.iter3 l0 F1 F2 F3 t)) Z
          else
            if P s0 s1 Z < (P l0 l2 Z).takeAt (P l0 l1 Z) then
              let F1 := T.fund4 l2
              let F2 := T.fund4 (T.drop s1 (P l0 l1 Z))
              P s0 (T.fund4 s1 (T.iter2 l0 F1 F2 t)) Z
            else t
      else P s0 (T.fund4 s1 t) Z
    | .Ω l l0 l1 l2 l3 =>
      if P s0 s1 Z < P l0 l3 Z then
        if s0 + 1 < l then
          let F1 := T.fund4 l3
          let F2 := fun x => P l0 (T.fund4 l2 x) Z
          let F3 := fun x => P l0 (T.fund4 l1 x) Z
          let F4 := fun x => P l0 (T.fund4 s1 x) Z
          P s0 (T.fund4 s1 (T.iter4 l0 F1 F2 F3 F4 t)) Z
        else
          if P s0 s1 Z < (P l0 l1 Z).takeAt (P l Z Z) then
            let F1 := T.fund4 l3
            let F2 := fun x => P l0 (T.fund4 l2 x) Z
            let F3 := fun x => P l0 (T.fund4 l1 x) Z
            let F4 := T.fund4 (T.drop s1 (P l Z Z))
            P s0 (T.fund4 s1 (T.iter4 l0 F1 F2 F3 F4 t)) Z
          else
            if P s0 s1 Z < (P l0 l2 Z).takeAt (P l0 l1 Z) then
              let F1 := T.fund4 l3
              let F2 := fun x => P l0 (T.fund4 l2 x) Z
              let F3 := T.fund4 (T.drop s1 (P l0 l1 Z))
              P s0 (T.fund4 s1 (T.iter3 l0 F1 F2 F3 t)) Z
            else
              let F1 := T.fund4 l3
              let F2 := T.fund4 (T.drop s1 (P l0 l2 Z))
              P s0 (T.fund4 s1 (T.iter2 l0 F1 F2 t)) Z
      else P s0 (T.fund4 s1 t) Z
  | P s0 s1 (P s20 s21 s22) =>
    P s0 s1 (T.fund4 (P s20 s21 s22) t)
termination_by s.size
decreasing_by
  all_goals (
    simp only [T.size]
    first
      | omega
      | (have hM2 := T.dom4_M2_size_lt _ _ _ _ _h1; omega)
      | (have hM1a := T.dom4_M1_l1_size_lt _ _ _ _ _ _h1; omega)
      | (have hM1b := T.dom4_M1_l2_size_lt _ _ _ _ _ _h1; omega)
      | (have hΩ1 := T.dom4_Ω_l1_size_lt _ _ _ _ _ _ _h1; omega)
      | (have hΩ2 := T.dom4_Ω_l2_size_lt _ _ _ _ _ _ _h1; omega)
      | (have hΩ3 := T.dom4_Ω_l3_size_lt _ _ _ _ _ _ _h1; omega)
      | (have hD := T.drop_size_le s1 (P l Z Z); omega)
      | (have hD := T.drop_size_le s1 (P l0 l1 Z); omega)
      | (have hD := T.drop_size_le s1 (P l0 l2 Z); omega)
  )

#eval fund4 (parse! "0^2^2^1^1^1^2^1^1^2") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^0^1^0^1^0^1^1") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^0^1^0^1^0^1^(1 + 1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^0^1^0^1^0^(1^1 + 1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^0^1^0^1^(0^1^1 + 0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^0^1^0^(1^0^1^1 + 1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^0^1^(0^1^0^1^1 + 0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^0^(1^0^1^0^1^1 + 1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^1^(0^1^0^1^0^1^1 + 0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^1^(1^0^1^0^1^0^1^1 + 1^0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^(1^1^0^1^0^1^0^1^1 + 1^1^0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^(0^1^1^0^1^0^1^0^1^1 + 0^1^1^0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^0^0^1^0^0^1^0^1") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^0^0^1^0^0^1^0^(1 + 1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^0^0^1^0^0^(1^0^1 + 1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^0^0^1^0^(0^1^0^1 + 0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^0^0^1^(0^0^1^0^1 + 0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^0^0^(1^0^0^1^0^1 + 1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^0^(0^1^0^0^1^0^1 + 0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^1^(0^0^1^0^0^1^0^1 + 0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^1^(1^0^0^1^0^0^1^0^1 + 1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^0^(1^1^0^0^1^0^0^1^0^1 + 1^1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^0^(0^1^1^0^0^1^0^0^1^0^1 + 0^1^1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval fund4 (parse! "0^(0^0^1^1^0^0^1^0^0^1^0^1 + 0^0^1^1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

inductive Dom where
| Zero
| One
| ω
| M (s : Nat)
| Ω (l l0 : Nat) (l1 : T) (args : List T)
deriving DecidableEq

def T.domChainBelow (s0 : Nat) (s1 : T) (l0 : Nat) : T → List T → Bool
| _, [] => false
| bound, w :: ws =>
  let term := P l0 w Z
  if P s0 s1 Z < term.takeAt bound then true
  else T.domChainBelow s0 s1 l0 term ws

def T.dom (M : Nat) : T → Dom
| Z => .Zero
| P s0 s1 Z =>
  match T.dom M s1 with
  | .Zero =>
    match s0 with
    | 0 => .One
    | _ + 1 =>
      match M with
      | 0 => .ω
      | _ + 1 => .M s0
  | .One => .ω
  | .ω => .ω
  | .M l =>
    if s0 < l then
      if M = 1 ∨ s0 + 1 < l then .ω
      else .Ω l s0 s1 []
    else .M l
  | .Ω l l0 l1 args =>
    let ln := args.getLastD l1
    if P s0 s1 Z < P l0 ln Z then
      if s0 + 1 < l then .ω
      else if args.length + 2 < M then
        if T.domChainBelow s0 s1 l0 (P l Z Z) (l1 :: args)
        then .ω
        else .Ω l l0 l1 (args ++ [s1])
      else .ω
    else .Ω l l0 l1 args
| P _ _ (P s0 s1 s2) => T.dom M (P s0 s1 s2)

def T.ValidArg (M : Nat) (s t : T) : Prop :=
  match T.dom M s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t
  | .M l => T.index_Prop t (P l Z Z)
  | .Ω _ l0 l1 args => T.index_Prop t (P l0 (args.getLastD l1) Z)

def T.iter0 (s0' : Nat) : T → T
| Z => Z
| P _ _ m2 =>
  let prev := iter0 s0' m2
  P s0' prev Z

def T.fund (M : Nat) (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 Z =>
    match T.dom M s1 with
    | .Zero =>
      match s0 with
      | 0 => Z
      | s0' + 1 =>
        match M with
        | 0 => T.iter0 s0' t
        | _ + 1 => t
    | .One => T.mul (P s0 (T.fund M s1 Z) Z) t
    | .ω => P s0 (T.fund M s1 t) Z
    | .M l => sorry
    | .Ω l l0 l1 args => sorry
  | P s0 s1 (P s20 s21 s22) =>
    P s0 s1 (T.fund M (P s20 s21 s22) t)
