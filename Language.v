 Require Import Coq.Logic.Classical.
 Require Import Coq.Logic.FunctionalExtensionality.
 Require Import Coq.Logic.PropExtensionality.
 
 Require Import Coq.Arith.PeanoNat.
 Require Import Coq.Lists.List.
 
 Import ListNotations.
 
 Section Language.
 
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
 
 Section SmallStepSemantics.
 
 (* We need an interpretation in which there are `restore' operations. *)
 
 Class InterpRestore :=
 { Prim_restore (x: var) (a: A): Prim
 ; Prim_restore_spec a x s: Prel (Prim_restore x a) s (update s x a) }.
 
 Context {IRes: InterpRestore}.
 
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
 
 Inductive bigstep : program -> state -> state -> Prop := 
   | BSprim O s t: Prel O s t -> bigstep (prim O) s t 
   | BScomp S1 S2 s t s': bigstep S1 s s' -> bigstep S2 s' t -> bigstep (comp S1 S2) s t.
 (* TODO: finish bigstep *)

 (* TODO: smallstep <-> bigstep *)

 Section Micro.

 Inductive microprogram : Set :=
   | mprog : program -> microprogram
   | mpar : microprogram -> microprogram -> microprogram
   | mchoice : microprogram -> microprogram -> microprogram
   | massert : Test -> microprogram.

 Coercion mprog : program >-> microprogram.

 Definition microconfig : Set := (microprogram*state)%type.
 
 (*
    (A1;A2) + B  --> A1; (A2 + (A1^-1);B)
    I(A1;A1^-1;B) = I(B)
    (A1;A1^-1, s) ->* (A1^-1, t) ->* (skip, s)
  *)
 Class InterpReverse :=
 { Prim_reverse (p : Prim) (s : state): Prim
 ; Prim_reverse_spec p s t: Prel p s t  -> Prel (Prim_reverse p s) t s }.

 Context {IRev: InterpReverse}.
 (*
  Properties:
    identities of reverse composition
    sequential reverse
    branch and reverse
    ite b S1 S2 -> if b then (S1; S2) else S3 -(b true)-> S1; S2 -(in s)-> (S2, s') -(b false)-> S1^-1; S3 
      (S1, s) -> (skip, s')
    reverse o reverse = id ?

 *)

 Inductive branchfree_program : Set :=
  | bfprim : Prim -> branchfree_program
  | bfskip : branchfree_program
  | bfhalt : branchfree_program
  | bflocal : var -> branchfree_program -> branchfree_program
  | bfcomp : branchfree_program -> branchfree_program -> branchfree_program.

 Fixpoint prog (bf : branchfree_program) : program :=
   match bf with
   | bfprim S1 => prim S1
   | bfskip => skip
   | bfhalt => halt
   | bflocal n S1 => local n (prog S1)
   | bfcomp S1 S2 => comp (prog S1) (prog S2)
   end.

 Coercion prog : branchfree_program >-> program.

 Definition isInvertible (p : program) : Prop :=
  exists p',  forall s t, bigstep p s t  -> bigstep p' t s.

 Definition isReversible (p : program) (s : state) (rev_p_s : program) : Prop :=
  forall t, bigstep p s t  -> bigstep rev_p_s t s.

 (*
 Inductive reverse (p : branchfree_program) (s : state) : branchfree_program :=
   match p with
   | bfprim S1 => bfprim (Prim_reverse S1 s)
   | bfskip => bfskip
   | bfhalt => bfhalt
   | bflocal n S1 => bflocal n (reverse S1 s) 
   | bfcomp S1 S2 => bfcomp (reverse S2 s) (reverse S1 s)
   end.
  *)


 Lemma bf_reversibility : forall p s, exists rev_p_s, isReversible p s rev_p_s.
 (*
    reverse (ite b S1 S2) = if (exists b') then (reverse S1) else (reverse S2) where b' is true in final state if b was true in initial state.
  *)
 Admitted.

 (*
 ...

    reverse (x:=-1; x^2) (x -> 10) =
    reverse x^2 (x -> -1); (reverse x:=-1 (x->10))


          (x -> 10) s [p]
          x:=-1;
          ||  /\?
          \/  || 
          x:=x^2;   
          (x -> 1, p') t [p']
          x:=10;
          (x -> 10) s

  Cost of speculation: cheapest program to revert (time/space).
  *)

 Definition isProg (mp : microprogram) (p : program) : Prop := mprog p = mp.
 Theorem eq_mp : forall p p', @eq microprogram (mprog p') (mprog p) <-> @eq (@program Sigma) p' p.
 intros. 
 split; intro; destruct p;inversion H; reflexivity.
 Qed.
 Theorem unique_isProg : forall mp p p', isProg mp p /\ isProg mp p' -> p = p'.
 intros.
 destruct H.
 unfold isProg in *. subst. 
 rewrite <- eq_mp. symmetry.
 apply H0.
 Qed.

 Definition exist_prog (mp : microprogram) : Prop := exists p, mprog p = mp.

 Definition toprog (mp : microprogram) : program := 
   match mp with
   | mprog p => p 
   | _ => skip
   end. 
 Coercion toprog : microprogram >-> program.

 Lemma getProgExist : forall mp, exist_prog mp -> isProg mp (toprog mp).
 intros.
 unfold exist_prog in H.
 unfold isProg.
 unfold toprog.
 destruct mp; try destruct H; try inversion H; reflexivity.
 Qed.


 Inductive microstep: microconfig -> microconfig -> Prop :=
 | MSmprog S S' s t: smallstep (S, s) (S', t) -> microstep (mprog S, s) (mprog S', t)
 | MSmparl S1 S2 S1' s t: microstep (S1, s) (S1', t) -> microstep (mpar S1 S2, s) (mpar S1' S2, t) 
 | MSmparr S1 S2 S2' s t: microstep (S2, s) (S2', t) -> microstep (mpar S1 S2, s) (mpar S1  S2', t) 
 | MSmchoice S1 S1' S2 RevS s s' t: isReversible S1 s RevS /\ exist_prog S2 -> 
                                              microstep (mprog S1, s) (S1', s') -> 
                                               microstep (mchoice S1 S2, s) (mchoice S1' (comp RevS S2), t).
     

 Record measures {A : Type} : Type := 
   {
   resource: list (A -> nat) (* list of operations *) 
   }.

 Definition measure : microprogram -> nat -> measure 

 Record wf_microprogram : Set :=
   {|
      mp : microprogram;
      wf_par : 
   |}

 Inductive microstep : program -> 


       







