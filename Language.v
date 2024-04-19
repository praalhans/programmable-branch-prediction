Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Import ListNotations.

Section Syntax.

(* Variables *)
Definition var := nat.
Definition var_dec (x y: var): {x = y} + {x <> y} := Nat.eq_dec x y.

(* Program signature *)
Class Signature :=
{ Prim: Set
; Test: Set
; Paccess: Prim -> list var
; Pchange: Prim -> list var
; Taccess: Test -> list var
}.

Context {Sigma: Signature}.

(* Programs *)
Inductive program :=
| prim: Prim -> program
| skip: program
| halt: program
| local: var -> program -> program
| comp: program -> program -> program
| ite: Test -> program -> program -> program
| while: Test -> program -> program.

Fixpoint access (S: program): list var :=
  match S with
  | prim O1 => Paccess O1
  | skip => []
  | halt => []
  | local x S1 => remove var_dec x (access S1)
  | comp S1 S2 => access S1 ++ access S2
  | ite T S1 S2 => Taccess T ++ access S1 ++ access S2
  | while T S1 => Taccess T ++ access S1
  end.

Fixpoint change (S: program): list var :=
  match S with
  | prim O1 => Pchange O1
  | skip => []
  | halt => []
  | local x S1 => remove var_dec x (change S1)
  | comp S1 S2 => change S1 ++ change S2
  | ite T S1 S2 => change S1 ++ change S2
  | while T S1 => change S1
  end.

End Syntax.

Print program.

Section SemanticBasis.

Class Domain := { A: Set }.

Context {D: Domain}.

(* Semantic domain: relations on state *)
Definition state := var -> A.
Definition state_eq (f g: state) := functional_extensionality f g.
(* state update *)
Definition update (f: state) (x: var) (a: A): state :=
  fun y => if var_dec x y then a else f y.
(* f and g differ in the variables xs *)
Definition diff (f g: state) (xs: list var): Prop :=
  forall x, ~In x xs -> f x = g x.
(* f and g are the same in the variables xs *)
Definition same (f g: state) (xs : list var): Prop :=
  forall x, In x xs -> f x = g x.
Proposition same_refl f xs: same f f xs.
unfold same; auto.
Qed.

Context {Sigma: Signature}.

Class Interp :=
{ Prel (O: Prim): state -> state -> Prop
; Prel_change O s t: Prel O s t -> diff s t (Pchange O)
; Prel_access O s t s': Prel O s t -> same s s' (Paccess O) -> exists t', Prel O s' t'
; Prel_det O s t s' t': Prel O s t -> Prel O s' t' -> same s s' (Paccess O) -> same t t' (Pchange O)
; Tset (T: Test): state -> Prop
; Tset_access T s s': same s s' (Taccess T) -> Tset T s -> Tset T s'
; Tset_dec T s: {Tset T s} + {~Tset T s}
}.

Context {I: Interp}.

Proposition Prel_access' O s t s':
  Prel O s t -> same s s' (Paccess O) -> exists t', Prel O s' t' /\ same t t' (Pchange O).
intros.
pose proof (Prel_access O s t s' H H0).
destruct H1 as (t' & H1).
exists t'. split; auto.
eapply Prel_det. apply H. apply H1. auto.
Qed.

Lemma Interp_determinism O s t t':
  Prel O s t -> Prel O s t' -> t = t'.
intros; apply state_eq; intros.
(* either x is in change or not *)
destruct (In_dec var_dec x (Pchange O)).
- pose proof (Prel_det _ _ _ _ _ H H0 (same_refl _ _)).
  apply H1; auto.
- pose proof (Prel_change _ _ _ H).
  pose proof (Prel_change _ _ _ H0).
  unfold diff in H1, H2.
  rewrite <- H1; auto.
Qed.

End SemanticBasis.

Section SmallStepSemantics.

Context {Sigma: Signature}.
Context {D: Domain}.

(* We need an interpretation in which there are `restore' operations. *)

Class InterpRestore (I: Interp) :=
{ Prim_restore (x: var) (a: A): Prim
; Prim_restore_spec a x s: Prel (Prim_restore x a) s (update s x a) }.

Context `{I: InterpRestore}.

Definition config := (program * state)%type.

Inductive smallstep: config -> config -> Prop :=
| SSprim O s t: Prel O s t -> smallstep (prim O, s) (skip, t)
| SSskip s: smallstep (skip, s) (skip, s)
| SShalt s: smallstep (halt, s) (halt, s)
| SSlocal x S1 s: smallstep (local x S1, s) (comp S1 (prim (Prim_restore x (s x))), s)
| SScomp S1 S2 s t: smallstep (S1, s) (skip, t) -> smallstep (comp S1 S2, s) (S2, t)
| SScomp' S1 S1' S2 s t: S1' <> skip -> smallstep (S1, s) (S1', t) -> smallstep (comp S1 S2, s) (comp S1' S2, t)
| SSite1 T S1 S2 s: Tset T s -> smallstep (ite T S1 S2, s) (S1, s)
| SSite2 T S1 S2 s: ~Tset T s -> smallstep (ite T S1 S2, s) (S2, s)
| SSwhile T S1 s: Tset T s -> smallstep (while T S1, s) (comp S1 (while T S1), s)
| SSwhile' T S1 s: ~Tset T s -> smallstep (while T S1, s) (skip, s).

Lemma determinism: forall c c' c'', smallstep c c' /\ smallstep c c'' -> c' = c''.
intros.
destruct H.
destruct c.
generalize dependent c'';
generalize dependent c';
generalize dependent s.
induction p; intros;
try (inversion H; inversion H0; try contradiction; reflexivity).
(* base case *)
+ inversion H; inversion H0; f_equal.
  apply (Interp_determinism p s t t0); auto.
(* sequential composition *)
+ inversion H; inversion H0.
  - pose proof (IHp1 _ _ H5 _ H10).
    inversion H11; auto.
  - pose proof (IHp1 _ _ H5 _ H11).
    inversion H12. exfalso. firstorder.
  - pose proof (IHp1 _ _ H6 _ H11).
    inversion H12. exfalso. firstorder.
  - pose proof (IHp1 _ _ H6 _ H12).
    inversion H13; auto.
Qed.
