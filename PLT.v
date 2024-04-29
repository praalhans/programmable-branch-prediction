Require Import Coq.Lists.List.

Import ListNotations.

Definition var := nat.

Section Syntax.

Class Primitive (PL: Set) := {
  prim: PL -> Prop
}.

Class Skip (PL: Set) := {
  skip: PL
}.

Class Comp (PL: Set) := {
  comp: PL -> PL -> PL
}.

Class Branching (PL: Set) (TL: Set) := {
  ite: TL -> PL -> PL -> PL
}.

Class Looping (PL: Set) (TL: Set) := {
  while: TL -> PL -> PL
}.

Class Imperative (PL: Set) (TL: Set)
    {the_prim: Primitive PL}
    {the_skip: Skip PL} {the_comp: Comp PL}
    {the_ite: Branching PL TL} {the_while: Looping PL TL} := {
  access: PL -> list var
; change: PL -> list var
; depends: TL -> list var
; access_skip: access skip = []
; change_skip: change skip = []
; access_comp S1 S2: access (comp S1 S2) = access S1 ++ access S2
; change_comp S1 S2: change (comp S1 S2) = change S1 ++ change S2
; access_ite B S1 S2: access (ite B S1 S2) = depends B ++ access S1 ++ access S2
; change_ite B S1 S2: change (ite B S1 S2) = change S1 ++ change S2
; access_while B S1: access (while B S1) = depends B ++ access S1
; change_while B S1: change (while B S1) = change S1
}.

Class Choice (PL: Set) := {
  choice: PL -> PL -> PL
}.

Class Parallel (PL: Set) := {
  par: PL -> PL -> PL
}.

Class Assert (PL: Set) (TL: Set) := {
  assert: TL -> PL
}.

Class Micro (PL: Set) (TL: Set) `{Imperative PL TL}
    {the_choice: Choice PL} {the_par: Parallel PL}
    {the_assert: Assert PL TL} := {
  access_choice S1 S2: access (choice S1 S2) = access S1 ++ access S2
; change_choice S1 S2: change (choice S1 S2) = change S1 ++ change S2
; access_par S1 S2: access (par S1 S2) = access S1 ++ access S2
; change_par S1 S2: change (par S1 S2) = change S1 ++ change S2
; access_assert B: access (assert B) = depends B
; change_assert B: change (assert B) = []
}.

End Syntax.
