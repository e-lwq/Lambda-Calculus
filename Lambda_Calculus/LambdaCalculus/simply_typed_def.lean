import LambdaCalculus.untyped_def
import Mathlib.Data.Set.Basic
open Set

open lt

inductive V
  | α
  | β
  | γ
  | δ
  | σ

inductive T
  | var : V → T
  | to : T → T → T
open T

set_option linter.style.longLine false
inductive isType : LambdaTerm → T → Prop
  | var : (v : Var) → (t : T) → isType (lt.var v) t
  | app {M N : LambdaTerm} {tm1 tm2 tn : T} : (hm : isType M (T.to tm1 tm2)) → (hn : isType N tm1) → isType (lt.app M N) tm2
  | abs {x : Var} {M : LambdaTerm} {tx tm : T} : (hx : isType (lt.var x) tx) → (hm : isType M tm) → isType (lt.abs x m) (T.to tx tm)

def typable (M : LambdaTerm) : Prop :=
  ∃ t : T, isType M t

inductive Λₜ
  | var : Var → Λₜ
  | app : Λₜ → Λₜ → Λₜ
  | abs : Var → T → Λₜ → Λₜ

namespace Typed
def FV (M : Λₜ) : Set Var :=
  match M with
  | Λₜ.var v => {v}
  | Λₜ.app m1 m2 => FV m1 ∪ FV m2
  | Λₜ.abs x _ M => FV M \ {x}
end Typed

abbrev Declaration := Prod Var T
abbrev Context := Set Declaration

def domain (context : Context) : Set Var :=
  Prod.fst '' context

-- legal / derivable judgements
inductive judgement : Context → Λₜ → T → Prop
  | var {x : Var} {t : T} (context : Context) (hx : ⟨x,t⟩ ∈ context) : judgement context (Λₜ.var x) t
  | appl {M N : Λₜ} {α β : T} (context : Context) (h1 : judgement context M (T.to α β)) (h2 : judgement context N α) : judgement context (Λₜ.app M N) β
  | abst {x : Var} {σ τ: T} {M : Λₜ} (context : Context) (hx : ⟨x,σ⟩ ∈ context) (hj : judgement context M τ) : judgement (context \ {⟨x,σ⟩}) (Λₜ.abs x σ M) (T.to σ τ)

def legal (M : Λₜ) : Prop := ∃ context : Context, ∃ ρ : T, judgement context M ρ

lemma freeVar {context : Context} {M : Λₜ} {t : T} : ∀ (jt : judgement context M t), Typed.FV M ⊆ domain context := by
  intro jt
  induction jt
  case' var x σ c hx =>
    unfold domain
    unfold Typed.FV
    intro y hy
    rw [hy]
    simp? [Set.mem_image]
    exact Exists.intro σ hx
  case' appl m n α β c h1 h2 ih1 ih2 =>
    unfold Typed.FV
    rw [Set.subset_def] at *
    intro y
    rw [Set.mem_union]
    intro hy
    cases hy with
    | inl hl =>
        exact ih1 y hl
    | inr hr =>
        exact ih2 y hr
  case' abst x σ τ m c hx hj ih =>
    unfold Typed.FV
    unfold domain
    rw [Set.subset_def] at *
    intro y hy
    rw [Set.mem_diff] at hy

    simp? [Set.mem_image]

    have ⟨⟨y1,y2⟩,⟨hw1,hw2⟩⟩ := ih y hy.left

    apply Exists.intro
    apply And.intro
    <;> simp? at hw2
    · rw [hw2] at hw1
      exact hw1

    have temp := hy.right
    intro a
    injection a with ha1 ha2
    exact temp ha1


lemma diff_union {α : Type} {s : Set α} {x : α} (hx : x ∈ s) : s \ {x} ∪ {x} = s := by
  ext y
  by_cases h : y = x
  · subst h
    simp? [hx]
    have := Classical.em (y∈ ({y} : Set α))
    cases this with
    | inl hl => exact Or.inr hl
    | inr hr => exact Or.inl hr
  · simp?
    apply Iff.intro
    · intro t
      cases t with
      | inl hl => exact hl.left
      | inr hr =>
        rw [hr] at h
        contradiction
    · intro t
      apply Or.inl
      exact And.intro t h

lemma union_diff {α : Type} {s : Set α} {x : α} : ¬ x ∈ s → s ∪ {x} \ {x} = s := by
  intro hx
  ext s
  apply Iff.intro
  simp?
  intro hs
  simp?
  exact hs

lemma thinning_lemma {Γ Γ': Context} {M : Λₜ} {σ : T} : judgement Γ M σ → Γ ⊆ Γ' → judgement Γ' M σ := by
  intro jt ss
  induction jt generalizing Γ'
  case' var x t c hx =>
    rw [Set.subset_def] at ss
    have := ss ⟨x,t⟩ hx
    exact judgement.var Γ' this
  case' appl m n α β c h1 h2 ih1 ih2 =>
    apply judgement.appl
    exact ih1 ss
    exact ih2 ss
  case' abst x σ τ m c hx ht ih =>
    have : c ⊆ (Γ' ∪ {⟨x,σ⟩}) := by
      rw [Set.subset_def]
      intro p
      by_cases p = ⟨x,σ⟩
      . rename_i ht
        intro hp
        exact Or.inr ht
      . rename_i ht
        intro hp
        rw [Set.subset_def] at ss
        simp?
        apply Or.inl
        apply ss p
        simp?
        exact And.intro hp ht
    have t1 := ih this
    have t2 : ⟨x,σ⟩ ∈ Γ' ∪ {⟨x,σ⟩} := by
      simp?
      exact Or.inr rfl
    have t3 := judgement.abst (Γ' ∪ {(⟨x,σ⟩)}) t2 t1
    sorry


lemma generation_var {Γ : Context} {x : Var} {σ : T} : judgement Γ (Λₜ.var x) σ → ⟨x,σ⟩ ∈ Γ := by
  intro jt
  cases jt with
  | var hxt =>
    rename_i ht
    exact ht

lemma generation_appl {Γ : Context} {m n : Λₜ} {τ : T}
  : judgement Γ (Λₜ.app m n) τ → ∃ σ : T, judgement Γ m (T.to σ τ) ∧ judgement Γ n σ := by
    intro jt
    cases jt with
    | appl tmp h1 h2 =>
      rename_i a
      apply Exists.intro
      exact ⟨h1,h2⟩

lemma generation_abst
  {Γ : Context} {x : Var} {M : Λₜ} {σ τ : T}
  : judgement Γ (Λₜ.abs x σ M) (T.to σ τ) → judgement (Γ ∪ {⟨x,σ⟩}) M τ := by
    intro jt
    cases jt with
    | abst c hx hj =>
      have : c \ {(⟨x,σ⟩)} ∪ {(⟨x,σ⟩)} = c :=
        diff_union hx
      rw [this]
      exact hj
