import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
open List

set_option linter.style.longLine false

abbrev TypeVar := Int

abbrev Var := String

inductive T
  | tv : TypeVar → T
  | to : T → T → T
  deriving BEq
local infixr:50 " to " => T.to

inductive Λₜ
  | Var : Var → Λₜ
  | Appl : Λₜ → Λₜ → Λₜ
  | Abst : Var → T → Λₜ → Λₜ
local infixl:50 " $ " => Λₜ.Appl

def FV (M : Λₜ) : Set Var :=
  match M with
  | Λₜ.Var v => {v}
  | Λₜ.Appl L N => FV L ∪ FV N
  | Λₜ.Abst x _ m => FV m \ {x}

def BV (M : Λₜ) : Set Var :=
  match M with
  | Λₜ.Abst x _ m => {x} ∪ BV m
  | Λₜ.Var _ => {}
  | Λₜ.Appl L N => BV L ∪ BV N

inductive Declaration (x : Var) (σ : T) : Prop

def Context : Type := Var → T

inductive Judgement : Context → Λₜ → T → Prop
  | JVar {Γ : Context} {x : Var} {σ : T} (hx : Γ x = σ) : Judgement Γ (Λₜ.Var x) σ
  | JAppl {Γ : Context} {M N : Λₜ} {σ τ : T} (hm : Judgement Γ M (σ to τ)) (hn : Judgement Γ N τ) : Judgement Γ (Λₜ.Appl M N) τ
  | JAbst {Γ : Context} {M : Λₜ} {x : Var} {σ τ : T} (hx : Γ x = σ) (hm : Judgement Γ M τ) : Judgement Γ (Λₜ.Abst x σ M) (σ to τ)

