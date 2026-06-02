import Mathlib.Data.Set.Basic
import LambdaCalculus.list_functions

inductive lt (t : Type)
  | var : t → lt t
  | app : lt t → lt t → lt t
  | abs : t → lt t → lt t
deriving DecidableEq, Repr

abbrev Var := String
abbrev LambdaTerm := lt Var

open lt

instance : Coe String LambdaTerm where
  coe := lt.var

def SyntaxEquiv (M N : LambdaTerm) : Prop :=
  M = N
local infixl:50 " ≅ " => SyntaxEquiv
namespace Subterm
def Sub (term : LambdaTerm) : Set LambdaTerm :=
  match term with
  | var v => {var v}
  | app M N => {app M N} ∪ Sub M ∪ Sub N
  | abs u M => {abs u M} ∪ Sub M

def isSubterm (M N : LambdaTerm) : Prop :=
  M ∈ Sub N

def isProperSubterm (M N : LambdaTerm) : Prop :=
  isSubterm M N ∧ ¬(SyntaxEquiv M N)

theorem reflexive : ∀ term : LambdaTerm, isSubterm term term := by
  intro term
  rw [isSubterm]
  unfold Sub
  cases term with
  | var v => simp; rfl
  | app M N => simp?; apply Or.inl; apply Or.inl; rfl
  | abs u M => simp?; apply Or.inl; rfl

theorem transitive : ∀ L M N : LambdaTerm, isSubterm L M ∧ isSubterm M N → isSubterm L N := by
  intro L M N cond
  induction N generalizing L M with
  | var n =>
    unfold isSubterm at *
    have : M = var n := cond.right
    rw [← this]
    exact cond.left
  | app n1 n2 ih1 ih2 =>
    unfold isSubterm at *
    cases cond.right with
    | inl c1 =>
      cases c1 with
      | inl c11 =>
        simp? at *
        have : M = n1.app n2 := c11
        rw [← this]
        have cl := cond.left
        exact cond.left
      | inr c12 =>
        simp? at *
        have := ih1 L M cond.left c12
        unfold Sub
        apply Or.inl
        apply Or.inr
        exact this
    | inr c2 =>
      simp? at *
      have := ih2 L M cond.left c2
      unfold Sub
      apply Or.inr
      exact this
  | abs v n ih =>
    simp? at *
    have cr := cond.right
    unfold isSubterm at cr
    unfold Sub at cr
    cases cr with
    | inl cr1 =>
      have : M = abs v n := cr1
      rw [← this]
      exact cond.left
    | inr cr2 =>
      have : isSubterm M n := cr2
      have := ih L M cond.left this
      unfold isSubterm
      unfold Sub
      apply Or.inr
      exact this

end Subterm

def FV (M : LambdaTerm) : Set Var :=
  match M with
  | var m => {m}
  | app m n => FV m ∪ FV n
  | abs x m => FV m \ {x}

def BoundedVar (M : LambdaTerm) : Set Var :=
  match M with
  | var _ => ∅
  | app m n => BoundedVar m ∪ BoundedVar n
  | abs x m => {x} ∪ BoundedVar m

def AllVar (M : LambdaTerm) : Set Var :=
  match M with
  | var m => {m}
  | app m n => AllVar m ∪ AllVar n
  | abs x m => {x} ∪ AllVar m

theorem AllVar.notInApp (y : Var) (m1 m2 : LambdaTerm) (hp : ¬(y ∈ AllVar (app m1 m2))) :
  ¬(y ∈ AllVar m1) ∧ ¬(y ∈ AllVar m2) := by
  unfold AllVar at hp
  simp? at hp
  exact hp

theorem AllVar.notInAbs (y : Var) (x : Var) (m : LambdaTerm) (hp : ¬(y ∈ AllVar (abs x m))) :
  ¬(y ∈ AllVar m) := by
  unfold AllVar at hp
  simp? at hp
  exact hp.right

def isClosed (M : LambdaTerm) : Prop :=
  FV M = ∅
abbrev isCombinator := isClosed

def Λ₀ : Type := {M : LambdaTerm // isClosed M}

-- Rename every FREE occurrence of x to y, given y does not appear in M at all
def rename (M : LambdaTerm) (x y : Var) (hp : ¬(y ∈ AllVar M)) : LambdaTerm :=
  match M with
  | var v =>
    if v == x then var y
    else var v
  | app m1 m2 =>
    have := AllVar.notInApp y m1 m2 hp
    app (rename m1 x y this.left) (rename m2 x y this.right)
  | abs v m =>
    if x == v then abs v m
    else
      have := AllVar.notInAbs y v m hp
      abs v (rename m x y this)

set_option linter.style.longLine false
inductive α_equiv : LambdaTerm → LambdaTerm → Prop
  | rfl {M : LambdaTerm} : α_equiv M M
  | symm {N M : LambdaTerm} : (α_equiv N M) → α_equiv M N
  | trans {M N L : LambdaTerm} : (α_equiv M L) → (α_equiv L N) → α_equiv M N
  | rename {x : Var} {M : LambdaTerm} {y : Var} {N : LambdaTerm} : (hp : ¬(y ∈ AllVar M)) → (N = rename M x y hp) → α_equiv (abs x M) (abs y N)
  | compat_appL {L M N : LambdaTerm} : (α_equiv M N) → α_equiv (app L M) (app L N)
  | compat_appR {M N L : LambdaTerm} : (α_equiv M N) → α_equiv (app M L) (app N L)
  | compat_abs {z : Var} {M N : LambdaTerm} : (α_equiv M N) → α_equiv (abs z M) (abs z N)

local infixl:50 " =α " => α_equiv
abbrev α_convertible := α_equiv
abbrev α_variant := α_equiv

-- Assume bounded variables of M are not in N
-- Substitute every FREE occurrence of x with N
def substitute (M : LambdaTerm) (x : Var) (N : LambdaTerm) : LambdaTerm :=
  match M with
  | var v =>
    if v == x then N
    else var v
  | app m1 m2 => app (substitute m1 x N) (substitute m2 x N)
  | abs v m =>
    if x == v then abs v m
    else abs v (substitute m x N)

theorem sub_lemma {M N L : LambdaTerm} {x y : Var} : (hxy : x≠y) → (hxL : ¬(x ∈ FV L))
  → substitute (substitute M x N) y L = substitute (substitute M y L) x (substitute N y L)
  := by sorry

namespace Barendregt_Convention

def BoundedVarList (M : LambdaTerm) : List Var :=
  match M with
  | var _ => []
  | app m n => BoundedVarList m ++ BoundedVarList n
  | abs x m => x :: BoundedVarList m

def FreeVarList (M : LambdaTerm) : List Var :=
  match M with
  | var m => [m]
  | app m n => FreeVarList m ++ FreeVarList n
  | abs x m => (FreeVarList m).filter (· ≠ x)

def is_B_Convention (M : LambdaTerm) : Bool :=
  have bvl := BoundedVarList M
  have fvl := FreeVarList M
  isDistinctList bvl && ListDisjoint bvl fvl

end Barendregt_Convention

namespace BetaReduction

def β_reduce (x : Var) (M N : LambdaTerm) : LambdaTerm :=
  substitute M x N

inductive β_reduction_1 : LambdaTerm → LambdaTerm → Prop
  | one_step_reduce (x : Var) (M N L : LambdaTerm) : β_reduction_1 (app (abs x M) N) (substitute M x N)
  | compat_appL {L M N : LambdaTerm} : β_reduction_1 M N → β_reduction_1 (app L M) (app L N)
  | compat_appR {M N L : LambdaTerm} : β_reduction_1 M N → β_reduction_1 (app M L) (app N L)
  | compat_abs {x : Var} {M N : LambdaTerm} : β_reduction_1 M N → β_reduction_1 (abs x M) (abs x N)

inductive β_reduction : LambdaTerm → LambdaTerm → Prop
  | rfl {M : LambdaTerm} : β_reduction M M
  | one_step {M N : LambdaTerm} : β_reduction_1 M N → β_reduction M N
  | trans {M1 M2 M3 : LambdaTerm} : β_reduction M1 M2 → β_reduction M2 M3 → β_reduction M1 M3
-- | α_equivL {M M0 N : LambdaTerm} : α_equiv M M0 → β_reduction M0 N → β_reduction M N--
-- | α_equivR {M Mn N : LambdaTerm} : α_equiv Mn N → β_reduction M Mn → β_reduction M N

inductive β_equiv : LambdaTerm → LambdaTerm → Prop
  | rfl {M : LambdaTerm} : β_equiv M M
  | one_stepR {M N : LambdaTerm} : β_reduction_1 M N → β_equiv M N
  | one_stepL {M N : LambdaTerm} : β_reduction_1 M N → β_equiv N M
  | trans {M1 M2 M3 : LambdaTerm} : β_equiv M1 M2 → β_equiv M2 M3 → β_equiv M1 M3

abbrev β_equal := β_equiv
abbrev β_convertible := β_equiv

theorem β_equiv_extends_steps {M N : LambdaTerm} (hmn : β_reduction M N) : β_equiv M N := by
  induction hmn with
  | rfl => exact β_equiv.rfl
  | one_step hmn => exact β_equiv.one_stepR hmn
  | trans _ _ ih1 ih2 => exact β_equiv.trans ih1 ih2

theorem β_equiv_symm {M N : LambdaTerm} (hmn : β_equiv M N) : β_equiv N M := by
  induction hmn with
  | rfl => exact β_equiv.rfl
  | one_stepR hmn => exact β_equiv.one_stepL hmn
  | one_stepL hmn => exact β_equiv.one_stepR hmn
  | trans _ _ ih1 ih2 => exact β_equiv.trans ih2 ih1

theorem β_equiv_trans {M1 M2 M3 : LambdaTerm} : β_equiv M1 M2 → β_equiv M2 M3 → β_equiv M1 M3 :=
  β_equiv.trans

theorem β_equiv_refl {M : LambdaTerm} : β_equiv M M :=
  β_equiv.rfl

end BetaReduction
open BetaReduction
local infixr:50 " →β " => β_reduction_1
local infixr:50 " ↠β " => β_reduction
local infixl:50 " =β " => β_equiv

def hasRedex (M : LambdaTerm) : Prop :=
  ∃ (x : Var) (m N : LambdaTerm),  M = app (abs x m) N

def β_NormalForm (M : LambdaTerm) : Prop :=
  ¬ hasRedex M

def isNormalFormFor (N M : LambdaTerm) : Prop :=
  β_NormalForm N ∧ M =β N

def β_Normalizing (M : LambdaTerm) : Prop :=
  ∃ N : LambdaTerm, isNormalFormFor N M

lemma normal_form_lemma (M : LambdaTerm) : β_NormalForm M → M ↠β N → M = N := by sorry

structure FiniteReductionPath where
  path : List LambdaTerm
  ll : path.length > 0
  hp : ∀ (i : ℕ), (h1 : 1 <= i) → (hl : i < List.length path) → β_reduction_1 path[i-1] path[i]
  hn : β_NormalForm path[path.length-1]

def WeakNormalizing (M : LambdaTerm) : Prop :=
  ∃ path : FiniteReductionPath, path.path[0]'path.ll = M
