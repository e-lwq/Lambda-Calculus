import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
open Finset

abbrev V := Int -- term variable
abbrev 𝕍 := Int -- type variable

inductive 𝕋2
  | v : 𝕍 → 𝕋2
  | to : 𝕋2 → 𝕋2 → 𝕋2
  | pi : 𝕍 → 𝕋2 → 𝕋2
  deriving DecidableEq, Repr
local infixr:50 " to " => 𝕋2.to

def 𝕋2.toString : 𝕋2 → String
  | .v t => ToString.toString t
  | .to α β => s!"({𝕋2.toString α}) → {𝕋2.toString β}"  -- Calls itself recursively
  | .pi α ρ => s!"Π{ToString.toString α}:*. {𝕋2.toString ρ}"


instance : ToString 𝕋2 where
  toString s := 𝕋2.toString s


inductive Λ
  | var : V → Λ
  | appl : Λ → Λ → Λ
  | absl : V → 𝕋2 → Λ → Λ
  | appt : Λ → 𝕋2 → Λ
  | abst : 𝕍 → Λ → Λ

local prefix:50 "LL " => Λ.absl
local prefix:50 "LT " => Λ.abst
local infixl:50 " appl " => Λ.appl
local infixl:50 " appt " => Λ.appt

def Subterm : Λ → Set Λ :=
  fun M =>
    {M} ∪ (
      match M with
      | .var _ => {}
      | .appl N L => Subterm N ∪ Subterm L
      | .absl _ _ N => Subterm N
      | .appt N _ => Subterm N
      | .abst _ N => Subterm N
    )

def FV_L : Λ → Finset V
  | .var x => {x}
  | .appl M N => FV_L M ∪ FV_L N
  | .absl x _ M => FV_L M \ {x}
  | .appt M _ => FV_L M
  | .abst _ M => FV_L M

def FT : 𝕋2 → Finset 𝕍
  | .v α => {α}
  | .to α β => FT α ∪ FT β
  | .pi α ρ => FT ρ \ {α}

def FV_T : Λ → Finset 𝕍
  | .var _ => {}
  | .appl M N => FV_T M ∪ FV_T N
  | .absl _ σ M => FT σ ∪ FV_T M
  | .appt M β => FT β ∪ FV_T M
  | .abst α M => FV_T M \ {α}

def maxInt : Nat → Nat → Nat :=
  fun a => fun b => if a >= b then a else b

def depthT (T : 𝕋2) : Nat :=
  match T with
  | .v _ => 1
  | .to a b => Nat.succ (Nat.max (depthT a) (depthT b))
  | .pi _ ρ => 1 + depthT ρ


def RenameT (T : 𝕋2) (α β : 𝕍) : 𝕋2 :=
  match T with
  | .v t => if t == α then .v β else .v t
  | .to γ δ => .to (RenameT γ α β) (RenameT δ α β)
  | .pi γ ρ => if γ == α then .pi γ ρ else .pi γ (RenameT ρ α β)

theorem renameSizeT : ∀ T : 𝕋2, ∀ α β : 𝕍, depthT T = depthT (RenameT T α β) := by
  intro T α β
  induction T
  case' v x =>
    by_cases hx : x = α
    · unfold RenameT
      rw [hx]
      simp?
      unfold depthT
      exact rfl
    · unfold RenameT
      simp [hx]
  case' _ a b ih1 ih2 =>
    unfold RenameT depthT
    rw [ih1, ih2]
  case' pi a ρ ih =>
    unfold RenameT
    by_cases hx : a = α
    · rw [hx]
      simp?
    · simp? [hx]
      unfold depthT
      rw [ih]

def RenameL (M : Λ) (x y : V) :=
  match M with
  | .var z => if z==x then Λ.var y else .var z
  | .appl N L => .appl (RenameL N x y) (RenameL L x y)
  | .absl z σ L => if z == x then .absl z σ L else .absl z σ (RenameL L x y)
  | .appt N β => .appt (RenameL N x y) β
  | .abst α N => .abst α (RenameL N x y)

def depthL (M : Λ) : Nat :=
  match M with
  | .var _ => 1
  | .appl N L => 1 + Nat.max (depthL N) (depthL L)
  | .absl _ _ N => 1 + depthL N
  | .appt N _ => 1 + depthL N
  | .abst _ N => 1 + depthL N

theorem renameSizeL : ∀ M : Λ, ∀ x y : V, depthL M = depthL (RenameL M x y) := by
  intro M x y
  induction M
  case var z =>
    unfold RenameL
    by_cases h : z = x
    · simp? [h]
      unfold depthL
      exact rfl
    · simp [h]
  · rename_i N L ih1 ih2
    unfold RenameL depthL
    rw [ih1, ih2]
  · rename_i z σ N ih
    unfold RenameL
    by_cases h : z = x
    · simp [h]
    · simp? [h]
      unfold depthL
      rw [ih]
  · rename_i N β ih
    unfold RenameL depthL
    simp? [ih]
  · rename_i α N ih
    unfold RenameL depthL
    simp? [ih]

def genNewInt (s : Finset Int) : Int := s.max.unbotD 0

set_option linter.style.longLine false
def SubT (ρ : 𝕋2) (α : 𝕍) (β : 𝕋2) : 𝕋2 :=
  match ρ with
  | .v x => if x == α then β else .v x
  | .to γ δ => .to (SubT γ α β) (SubT δ α β)
  | .pi γ ρ => let tmp := genNewInt (FT β)
                let δ := if tmp > α then tmp + 1 else α + 1
                .pi δ (SubT (RenameT ρ γ δ) α β)
  termination_by depthT ρ
  decreasing_by
  · conv_rhs => simp [depthT]
    by_cases depthT γ >= depthT δ <;> simp?
  · conv_rhs => simp [depthT]
    by_cases depthT γ >= depthT δ <;> simp?
  · have hr : depthT ρ = depthT (RenameT ρ γ (if h : genNewInt (FT β) > α then genNewInt (FT β) + 1 else α + 1))
        := renameSizeT ρ γ (if h : genNewInt (FT β) > α then genNewInt (FT β) + 1 else α + 1)
    rw [Eq.symm hr]
    conv_rhs => simp [depthT]
    simp?


def SubL (M : Λ) (x : V) (N : Λ) : Λ :=
  match M with
  | .var y => if x == y then N else .var y
  | .appl P Q => .appl (SubL P x N) (SubL Q x N)
  | .appt P β => .appt (SubL P x N) β
  | .abst α L => .abst α (SubL L x N)
  | .absl y σ L =>let tmp := genNewInt (FV_L N)
                  let z := if tmp > x then tmp + 1 else x + 1
                  .absl z σ (SubL (RenameL L y z) x N)
  termination_by depthL M
  decreasing_by
  · conv_rhs => simp [depthL]
    by_cases h : depthL P >= depthL Q
    · simp? [h]
    · have h_lt : depthL P < depthL Q := by rwa [not_le] at h
      have h_lte : depthL P <= depthL Q := le_of_lt h_lt
      simp? [h_lte]
      have : depthL Q < 1 + depthL Q := by simp?
      exact lt_trans h_lt this
  · conv_rhs => simp [depthL]
    by_cases h : depthL Q >= depthL P
    · simp? [h]
    · have h_lt : depthL Q < depthL P := by rwa [not_le] at h
      have h_lte : depthL Q <= depthL P := le_of_lt h_lt
      simp? [h_lte]
      have : depthL P < 1 + depthL P := by simp?
      exact lt_trans h_lt this
  · conv_rhs => simp [depthL]
    simp?
  · conv_rhs => simp [depthL]
    simp?
  · conv_rhs => simp [depthL]
    have : depthL L = depthL (RenameL L y (if h : genNewInt (FV_L N) > x then genNewInt (FV_L N) + 1 else x + 1))
      := renameSizeL L y (if h : genNewInt (FV_L N) > x then genNewInt (FV_L N) + 1 else x + 1)
    simp? [this]

inductive Context
  | Nil : Context
  | ConsT (Γ : Context) (α : 𝕍) : Context
  | ConsL (Γ : Context) (x : V) (σ : 𝕋2) : Context


def inContext (x : V) (σ : 𝕋2) (Γ : Context) : Prop :=
  match Γ with
  | .Nil => false
  | .ConsT Γ' _ => inContext x σ Γ'
  | .ConsL Γ' x' σ' => (x = x' ∧ σ = σ') ∨ inContext x σ Γ'

def domL : Context → Finset V
  | .Nil => {}
  | .ConsT Γ _ => domL Γ
  | .ConsL Γ x _ => {x} ∪ domL Γ

def domT : Context → Finset 𝕍
  | .Nil => {}
  | .ConsT Γ α => {α} ∪ domT Γ
  | .ConsL Γ _ _ => domT Γ

def ValidContext : Context → Prop
  | .Nil => true
  | .ConsT Γ α => ¬ α ∈ domT Γ ∧ ValidContext Γ
  | .ConsL Γ x σ => ¬ x ∈ domL Γ ∧ FT σ ⊆ domT Γ ∧ ValidContext Γ

set_option linter.style.longLine false
inductive Judgement : Sum (Context × Λ × 𝕋2) (Context × 𝕋2) → Prop
  | var {x : V} {σ : 𝕋2} {Γ : Context} (hg : ValidContext Γ) (hx : inContext x σ Γ) : Judgement (.inl ⟨Γ, .var x, σ⟩)
  | form {β : 𝕋2} {Γ : Context} (hg : ValidContext Γ) (hb : FT β ⊆ domT Γ) : Judgement (.inr ⟨Γ,β⟩)
  | absl {M : Λ} {Γ : Context} {x : V} {σ τ: 𝕋2} (hg : ValidContext Γ) (hx : ¬ x ∈ domL Γ) (hσ : FT σ ⊆ domT Γ) (hm : Judgement (.inl ⟨.ConsL Γ x σ, M, τ⟩)) : Judgement (.inl ⟨Γ, .absl x σ M, .to σ τ⟩)
  | appl {M N : Λ} {Γ : Context} {σ τ : 𝕋2} (hg : ValidContext Γ) (hm : Judgement (.inl ⟨Γ, M, .to σ τ⟩)) (hn : Judgement (.inl ⟨Γ, N, σ⟩)) : Judgement (.inl ⟨Γ, .appl M N, τ⟩)
  | appt {M : Λ} {Γ : Context} {α : 𝕍} {β ρ : 𝕋2} (hg : ValidContext Γ) (hm : Judgement (.inl ⟨Γ, M, .pi α ρ⟩)) (hn : Judgement (.inr ⟨Γ, β⟩)) : Judgement (.inl ⟨Γ, .appt M β, SubT ρ α β⟩)
  | abst {M : Λ} {Γ : Context} {α : 𝕍} {ρ : 𝕋2} (hg : ValidContext Γ) (ha : ¬ α ∈ domT Γ) (hm : Judgement (.inl ⟨.ConsT Γ α, M, ρ⟩)) : Judgement (.inl ⟨Γ, .abst α M, .pi α ρ⟩)

-- CHURCH NUMERALS --
abbrev NAT : 𝕋2 := .pi α (.to (.to (.v α) (.v α)) (.to (.v α) (.v α))) where α : 𝕍 := 1

def ZERO : Λ := .abst α (.absl f (.to (.v α) (.v α)) (.absl x (.v α) (.var x)))
                where
                  α := 1
                  f := 2
                  x := 3

def ONE : Λ := .abst α (.absl f (.to (.v α) (.v α)) (.absl x (.v α) ((.var f) appl (.var x))))
                where
                  α := 1
                  f := 2
                  x := 3

def TWO : Λ := .abst α (.absl f (.to (.v α) (.v α)) (.absl x (.v α) ((.var f) appl ((.var f) appl (.var x)))))
                where
                  α := 1
                  f := 2
                  x := 3

def SUC : Λ := .absl x NAT (.abst β (.absl f (.to (.v β) (.v β)) (.absl y (.v β) ((.var f) appl ((.var x) appt (.v β) appl (.var f) appl (.var y))))))
                where
                  x := 1
                  β := 2
                  f := 3
                  y := 4

def ADD : Λ := .absl m NAT (.absl n NAT (.abst β (.absl f (.to (.v β) (.v β)) (.absl x (.v β) ((.var m) appt (.v β) appl (.var f) appl ((.var n) appt (.v β) appl (.var f) appl (.var x)))))))
                where
                  m := 1
                  n := 2
                  β := 3
                  f := 4
                  x := 5

def MUL : Λ := .absl m NAT (.absl n NAT (.abst β (.absl f (.to (.v β) (.v β)) (.absl x (.v β) ((.var m) appt (.v β) appl ((.var n) appt (.v β) appl (.var f)) appl (.var x))))))
                where
                  m := 1
                  n := 2
                  β := 3
                  f := 4
                  x := 5

-- BOOLEAN LOGIC --
def BOOL : 𝕋2 := .pi α (.to (.v α) (.to (.v α) (.v α)))
                  where
                    α := 1

def TRUE : Λ := .abst α (.absl x (.v α) (.absl y (.v α) (.var x)))
                where
                  α := 1
                  x := 2
                  y := 3

def FALSE : Λ := .abst α (.absl x (.v α) (.absl y (.v α) (.var y)))
                where
                  α := 1
                  x := 2
                  y := 3

def NEG : Λ := .absl n BOOL (.abst α (.absl x (.v α) (.absl y (.v α) ((.var n) appt (.v α) appl (.var y) appl (.var x)))))
                where
                  n := 1
                  α := 2
                  x := 3
                  y := 4

abbrev BOOL_OP (a1 a2 b1 b2 : Bool) : Λ :=
  .absl u BOOL (.absl v BOOL (.abst α (.absl x (.v α) (.absl y (.v α) ((.var u) appt (.v α) appl ((.var v) appt (.v α) appl (.var a1') appl (.var a2')) appl ((.var v) appt (.v α) appl (.var b1') appl (.var b2')))))))
  where
    u := 1
    v := 2
    α := 3
    x := 4
    y := 5
    a1' := if a1 then x else y
    a2' := if a2 then x else y
    b1' := if b1 then x else y
    b2' := if b2 then x else y

def AND : Λ := BOOL_OP True False False False
def OR : Λ := BOOL_OP True True True False
def XOR : Λ := BOOL_OP False True True False
def IMPL : Λ := BOOL_OP True False True True

def ISZERO : Λ := .absl n NAT ((.var n) appt BOOL appl (.absl x BOOL FALSE) appl TRUE)
                  where
                    n := 1
                    x := 2

def betaReduce (M N : Λ) :=
  match M with
  | .absl x _ M' => SubL M' x N
  | _ => .var (-1)

-- TREE --
def TREE : 𝕋2 := .pi α ((BOOL to (.v α)) to (BOOL to (.v α) to (.v α) to (.v α)) to (.v α))
                  where α := 1
