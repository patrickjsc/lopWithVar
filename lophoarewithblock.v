Require Import Coq.Strings.String.
Require Import List.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.ListSet.

Inductive exp : Type :=
  | ANum : nat -> exp
  | APlus : exp -> exp -> exp
  | AMinus : exp -> exp -> exp
  | AMult : exp -> exp -> exp
  | AVar : string -> exp
  | BTrue : exp
  | BFalse : exp
  | BEq : exp -> exp -> exp
  | BLe : exp -> exp -> exp
  | BNot : exp-> exp
  | BAnd : exp-> exp-> exp
  | BCond : exp-> exp-> exp-> exp.

Infix "==" := eq (at level 70, no associativity).

Inductive command : Type := 
  |SKIP : command
  |ABORT : command
  |assgnment : list string -> list exp -> command (*Dependent Types*)
  |seqcomp : command -> command -> command
  |conditional : exp-> command -> command -> command
  |nondeterminism : command -> command -> command
  |varDeclaration : string -> command -> command.

Infix ";" := seqcomp (at level 70, no associativity).
Infix "::=" := assgnment (at level 65, no associativity).


Definition substitution := string -> option exp.

Fixpoint subst (s:substitution) (e :exp) : exp :=
  match e with
  |AVar y => match s y with
             |None => AVar y
             |Some e1 => e1 end
  |ANum n => ANum n
  |APlus e1 e2 => APlus (subst s e1) (subst s e2)
  |AMinus e1 e2 => AMinus (subst s e1) (subst s e2)
  |AMult e1 e2 => AMult (subst s e1) (subst s e2)
  |BTrue => BTrue
  |BFalse => BFalse
  |BEq e1 e2 =>  BEq (subst s e1) (subst s e2) 
  |BLe e1 e2 =>  BLe (subst s e1) (subst s e2) 
  |BNot e1 => BNot (subst s e1)
  |BAnd e1 e2 =>BAnd (subst s e1) (subst s e2)
  |BCond e1 e2 e3 => BCond (subst s e1) (subst s e2) (subst s e3)
end.


Definition substL (s :substitution) (es :list exp) : list exp := map (subst s) es.

Fixpoint consSubst (lstr : list string) (lex : list exp) (x: string) : option exp :=
match lstr, lex, x with
|lstr::lstrs, lex::lexs, x => if string_dec x lstr then Some lex else consSubst lstrs lexs x
|_,_,x => None
end.

Infix "|->" := consSubst (at level 70, no associativity).
Notation " '[' e ']' " := (conditional e SKIP ABORT) (at level 80, no associativity) .

Variable isdef : exp -> exp.

Fixpoint vars (exp : exp) : set string :=
match exp with
|AVar y => y::nil
|ANum y => nil
|APlus e1 e2 => vars e1 ++ vars e2
|AMinus e1 e2 => vars e1 ++ vars e2
|AMult e1 e2 => vars e1 ++ vars e2
|BTrue => nil
|BFalse => nil
|BEq e1 e2 =>  vars e1 ++ vars e2
|BLe e1 e2 =>  vars e1 ++ vars e2 
|BNot e1 => vars e1 
|BAnd e1 e2 =>vars e1 ++ vars e2
|BCond e1 e2 e3 => vars e1 ++ vars e2 ++ vars e3
end.

Fixpoint free (c:command) : set string :=
match c with
|SKIP => empty_set string 
|ABORT => empty_set string
|assgnment xs es => xs ++ concat (map vars es)
|conditional b c1 c2 => vars b ++ free c1 ++ free c2
|nondeterminism c1 c2 => free c1 ++ free c2
|varDeclaration x c1 => x::nil ++ free c1
|seqcomp c1 c2 => free c1 ++ free c2
end.

(*Renomeia variáveis livres*)
Fixpoint rename (c:command) (x y : string) : command  :=
match c with
|SKIP => SKIP
|ABORT => ABORT
|assgnment xs es => assgnment 
                       (map (fun z => if string_dec x z then y else x ) xs) 
                       (map (subst (x::nil|->AVar y::nil)) es)
|conditional b c1 c2 => conditional (subst (x::nil|->AVar y::nil) b) (rename c1 x y) (rename c2 x y)
|seqcomp c1 c2 => seqcomp (rename c1 x y) (rename c2 x y)
|nondeterminism c1 c2 => nondeterminism (rename c1 x y) (rename c2 x y)
|varDeclaration z c1 => if string_dec x z 
                        then varDeclaration z c1 
                        else varDeclaration z (rename c1 x y)
end.

Fixpoint substC (c:command) (x:string) (e: exp) : command :=
match c with
|SKIP => SKIP
|ABORT => ABORT
|assgnment xs es => assgnment xs
                       (map (subst (x::nil|->e::nil)) es)
|conditional b c1 c2 => conditional (subst (x::nil|->e::nil) b) (substC c1 x e) (substC c2 x e)
|seqcomp c1 c2 => seqcomp (substC c1 x e) (substC c2 x e)
|nondeterminism c1 c2 => nondeterminism (substC c1 x e) (substC c2 x e)
|varDeclaration z c1 => if string_dec x z 
                        then varDeclaration z c1 
                        else varDeclaration z (substC c1 x e)
end.

Fixpoint readonly (x:string)(c:command) : Prop :=
match c with
|SKIP => True
|ABORT => True
|assgnment xs es => ~(In x xs) 
|conditional b c1 c2 => (readonly x c1)/\(readonly x c2)
|seqcomp c1 c2 => (readonly x c1)/\(readonly x c2)
|nondeterminism c1 c2 => (readonly x c1)/\(readonly x c2)
|varDeclaration z c1 => (x=z)\/(readonly x c1)
end.

Infix "," := app (at level 60, no associativity).

(*6.9*)
Axiom var_01:
forall (x:string) (b c : command),
varDeclaration x (nondeterminism b c) == nondeterminism (varDeclaration x b) (varDeclaration x c).
(*6.10*)
Axiom var_02:
forall (e : exp) (b c : command) (x: string),
varDeclaration x (conditional e b c) == conditional e (varDeclaration x b) (varDeclaration x c).
(*6.11*)
Axiom var_03:
forall (x:string) (p:list string) (e:list exp) (d : exp) (c:command),
varDeclaration x (c;((p,(x::nil))::=(e,(d::nil)))) == varDeclaration x (c;[isdef d]; p::=e).
(*6.12*)
Axiom var_04:
forall (x y: string) (c: command),
x<>y->
varDeclaration x (varDeclaration y c) == varDeclaration y (varDeclaration x c).
(*6.14*)
Axiom var_06:
forall (c d : command) (x: string),
~(In x (free c)) ->
c ; (varDeclaration x d) == varDeclaration x (c;d).
(*6.15*)
Axiom var_07:
forall (c d : command) (x: string),
~(In x (free d)) ->
(varDeclaration x c) ; d   == varDeclaration x (c;d).
(*6.16*)
Axiom var_08:
forall (c : command) (x: string),
~(In x (free c)) ->
(varDeclaration x c) == c.
(*6.17*)
Axiom var_09:
forall (c : command) (x y: string),
~(In y (free c)) ->
varDeclaration x c  == varDeclaration y c.




(** Axiomas sobre Nondeterminism*)
Axiom nondeterminism_symmetry : 
forall (P Q : command), nondeterminism P Q == nondeterminism Q P .
Axiom nondeterminism_associativity : 
forall (P Q R :command), nondeterminism P (nondeterminism Q R) == nondeterminism (nondeterminism P Q) R.
Axiom nondeterminism_idempotence :
forall (P:command) , 
nondeterminism P P == P .
Axiom nondeterminism_zeroAbort :
forall (P:command) , nondeterminism P ABORT == ABORT.


(** Axiomas para condicional*)

Axiom conditional_true_1 :
forall (P Q : command), conditional BTrue P Q == P.
Axiom conditional_false_2 : 
forall (P Q : command), conditional BFalse P Q == Q.
Axiom conditional_idempotence_3:
forall (P : command) (b:exp), conditional b P P == P.
Axiom conditional_associative_4 :
forall (P Q R :command) (b:exp), conditional b P (conditional b Q R) == conditional b (conditional b P Q) R.
Axiom conditional_neg1_5 :
forall (P Q :command) (b : exp), conditional b P Q == conditional (BNot b) Q P.
Axiom conditional_cond_6 :
forall (P Q : command) (b c d : exp), conditional (BCond b c d) P Q  == conditional b (conditional c P Q) (conditional d P Q).
Axiom conditional_middle_7 :
forall (P Q R: command) (b : exp), conditional b P (conditional b Q R) == conditional b P R. 
Axiom conditional_nondeterminism_8:
forall (P Q R : command) (b : exp), 
conditional b (nondeterminism P Q) R == nondeterminism (conditional b P R) (conditional b Q R).
Theorem conditional_nondeterminism_9 : forall (P Q R : command) (b:exp), 
conditional b R (nondeterminism P Q) == nondeterminism (conditional b R P) (conditional b R Q).
Proof. 
intros P Q R b.
rewrite conditional_neg1_5. 
rewrite conditional_nondeterminism_8. 
rewrite <- conditional_neg1_5. 
rewrite <- conditional_neg1_5. 
reflexivity. Qed.
Axiom conditional_nondeterminism_10 :
forall (P Q R : command) (b : exp), 
nondeterminism (conditional b P Q) R == conditional b (nondeterminism P R) (nondeterminism Q R).
Axiom conditional_cond_11:
forall (P Q R : command) (b c : exp),
conditional c (conditional b P Q) R == conditional b (conditional c P R) (conditional c Q R). 
Theorem conditional_cond_12 : forall ( P Q R : command) (b c d: exp),
conditional b (conditional c P R) (conditional d Q R) == conditional (BCond b c d) (conditional b P Q) R.
intros P Q R b c d.
rewrite conditional_cond_6.
symmetry. 
rewrite conditional_cond_11. Admitted.

(* Axiomas para sequential composition*)


Axiom seqcomp_associativity_1 :
forall (P Q R : command) , seqcomp P (seqcomp Q R) == seqcomp (seqcomp P Q) R.
Axiom seqcomp_unitSKIP_2 :
forall (P : command), seqcomp SKIP P == seqcomp P SKIP.
Axiom seqcomp_unitSKIP2_2 :
forall (P : command), seqcomp P SKIP == P.
Theorem seqcomp_unitSKIP3_2 :
forall (P : command), seqcomp SKIP P == P.
Proof.
intros P.
rewrite seqcomp_unitSKIP_2.
rewrite seqcomp_unitSKIP2_2.
reflexivity. Qed.
Axiom seqcomp_zeroABORT1_3 :
forall (P :command) , seqcomp ABORT P == seqcomp P ABORT.
Axiom seqcomp_zeroABORT2_3 :
forall (P :command) , seqcomp P ABORT == ABORT.
Theorem seqcomp_zeroABORT3_3:
forall (P : command) , seqcomp ABORT P == ABORT.
Proof.
intros P.
rewrite seqcomp_zeroABORT1_3.
rewrite seqcomp_zeroABORT2_3.
reflexivity. Qed.
Axiom seqcomp_disjunctive1_4 :
forall (P Q R : command), seqcomp (nondeterminism P Q) R == nondeterminism (seqcomp P R) (seqcomp Q R).
Axiom seqcomp_disjunctive2_4 :
forall (P Q R : command),
seqcomp R (nondeterminism P Q) == nondeterminism (seqcomp R P) (seqcomp R Q).
Axiom seqcomp_conditional_5 :
forall (P Q R : command) (b : exp),
seqcomp (conditional b P Q) R == conditional b (seqcomp P R) (seqcomp Q R).

Theorem seq: SKIP == seqcomp SKIP SKIP.
Proof.
rewrite seqcomp_unitSKIP3_2.
reflexivity. Qed.

(**Assigment**)

Axiom assigment_1:
forall (x:list string) (E F : list exp),
length x = length E ->
length x = length F ->
NoDup x ->
x::=E ; x::=F == x ::= (substL (consSubst x E) F).

Axiom assigment_2:
forall (x:list string),
  assgnment x (map AVar x) == SKIP.

Axiom assigment_3:
forall (x y:list string) (e:list exp),
length x = length e ->
assgnment (x++y) (e ++ (map AVar y)) == assgnment x e.

Axiom assigment_4: 
forall (x y z: list string) (E F G:list exp),
(length x = length E) ->
(length y = length F) -> 
(length z = length G) ->
assgnment (x++y++z) (E++F++G) = assgnment (y++x++z) (F++E++G).

Axiom assigment_4_0:
forall (x y z: list string) (E F G:list exp),
(length x = length E) ->
(length y = length F) ->
(length z = length G) ->
assgnment ((x++y)++z) ((E++F)++G) = assgnment ((z++x)++y) ((G++E)++F).

Corollary assigment_4_1 :
forall (x y: list string) (E F:list exp),
(length x = length E) /\ (length y = length F) ->
assgnment (x++y) (E++F) = assgnment (y++x) (F++E).
Proof.
intros x y E F H.
assert(x++y=x++y++nil) as H1.
  +rewrite app_nil_r. reflexivity. + rewrite H1.
assert(E++F=E++F++nil) as H2.
  -rewrite app_nil_r. reflexivity. - rewrite H2.
assert(y++x=y++x++nil) as H3.
  {rewrite app_nil_r. reflexivity. }rewrite H3.
assert(F++E=F++E++nil) as H4.
  {rewrite app_nil_r. reflexivity. }rewrite H4.
apply assigment_4;intuition. Qed.


Axiom assigment_5 :
forall (x : list string) (E: list exp) (P Q : command) (b : exp),
length x = length E ->
NoDup x ->
((x ::= E) ; (conditional b P Q)) == 
(conditional  b ((x::=E);P) ((x::=E);Q)).

(*
Axiom assigment_6 :
forall (x: list string) (E F : list exp) (b : exp),
(conditional b (x ::= E) (x::= F)) ==
(x ::= (conditional b E F)).

*)

Lemma subst_1 :
forall (x:list string) (e:exp),
subst (x |->map AVar x) e = e.
Proof.
intros x e. 
induction e.
+auto.
+simpl. rewrite IHe1; rewrite IHe2; reflexivity.
+simpl. rewrite IHe1. rewrite IHe2. reflexivity.
+simpl. rewrite IHe1. rewrite IHe2. reflexivity.
+ induction x. 
-simpl. reflexivity.
-simpl. destruct (string_dec s a).
 {rewrite e. reflexivity. }
 {simpl in IHx. apply IHx. }Qed.

Lemma subst_nilnil :
forall (e:exp),
subst (nil |-> nil) e = e.
Proof.
intros e.
rewrite subst_1. reflexivity. Qed.

Definition overWrite s1 s2 : substitution :=
  fun x => match s2 x with
           | None => s1 x
           | Some e => Some e
          end.


Lemma overWrite_app:
forall (x y:list string) (F G:list exp),
  length x = length F -> length y = length G ->
     overWrite (y |-> G) (x |->F) = ( x++y |-> F++G ).
Proof.
induction x.
+intros.
 simpl in H.
 assert (F = nil).
 apply length_zero_iff_nil.
 auto.
 rewrite H1.
 simpl.
 unfold overWrite.
 apply functional_extensionality.
 auto.

+intros.
 destruct F.
 -simpl in H.
  symmetry in H.
  apply Coq.Init.Peano.O_S in H.
  contradiction.
 -simpl.
  unfold overWrite.
  assert
   (forall x0, 
    (fun x0 =>
     match (if string_dec x0 a then Some a0 else (x |-> F) x0) with
     | Some e0 => Some e0
     | None => (y |-> G) x0
     end) x0 = (fun x0 =>
                if string_dec x0 a
                then Some a0
                else overWrite (y |-> G) (x |-> F) x0) x0).
  {intros.
   destruct (string_dec x0 a).
   auto.
   auto. }
   apply functional_extensionality in H1.
   rewrite H1.
   rewrite IHx.
   auto. auto. auto. Qed.

Lemma consSubst_app :
forall x y F G s,
  length x = length F -> length y = length G ->
    (x++y |-> F++G) s = if in_dec string_dec s x
                        then (x |-> F) s
                        else (y |-> G) s.
Proof.
induction x.
+intros; simpl.
 simpl in H.
 symmetry in H.
 apply length_zero_iff_nil in H.
 rewrite H.
 auto.
+intros.
 destruct F.
 simpl in H.
 symmetry in H.
 apply O_S in H.
 contradiction.
 destruct (in_dec string_dec s (a :: x)).
 -destruct (string_dec s a).
  {rewrite e; simpl.
   destruct (string_dec a a).
   auto.
   rewrite IHx.
   { intuition . }
   { intuition. }
   {auto. }
  }
  {simpl.
   destruct (string_dec s a).
   {auto. }
   {assert (In s x).
    simpl in i.
    destruct i.
    {symmetry in H1.
     contradiction. }
    {auto. } 
    rewrite IHx.
    {destruct (in_dec string_dec s x ).
     {auto. }
     {contradiction. }
    }
    {auto. }
    {auto. }
   } }
 -simpl.
  assert (s <> a).
  {simpl in n.
   auto. }
  destruct (string_dec s a).
  {contradiction. }
  {rewrite IHx.
   {simpl in n.
    assert (~ In s x).
    auto.
    destruct (in_dec string_dec s x).
    {contradiction. }
    { auto. } }
    auto.
    auto. }
Qed.



Lemma consSubst_app_1 :
forall x y F G s,
  length x = length F -> length y = length G -> In s x ->
    (x++y |-> F++G) s = (x |-> F) s.
Proof.
induction x.
+intros; simpl in H1; contradiction.
+intros.
 destruct F.
 -simpl in H; symmetry in H; apply O_S in H; contradiction.
 -simpl in H1.
  destruct H1.
  {rewrite H1.
   simpl.
   destruct (string_dec s s).
   {auto. }
   {intuition. } }
  {simpl.
   destruct (string_dec s a).
   {auto. }
   {apply IHx.
    auto.  auto.  auto.  } } 
Qed.


Lemma consSubst_app_2 :
forall x y F G s,
  length x = length F -> length y = length G -> ~ In s x ->
    (x++y |-> F++G) s = (y |-> G) s.
Proof.
induction x.
+intros.
 simpl in H.
 symmetry in H.
 apply length_zero_iff_nil in H.
 rewrite H.
 auto.
+intros.
 destruct F.
 -simpl in H. symmetry in H. apply O_S in H. contradiction.
 -simpl in H1.
  assert (a <> s /\ ~In s x).
  auto.
  destruct H2.
  simpl.
  destruct (string_dec s a).
  {symmetry in e. contradiction. }
  {apply IHx.
   +auto.
   +auto.
   +auto. }
Qed.


Lemma length_nil_eqNil (A:Type) :
forall (F:list A),
   length F = length (nil:list A) <-> (F = nil).
Proof.
intros.
simpl.
split.
intro.
symmetry in H.
apply length_zero_iff_nil.
auto.
intro.
apply length_zero_iff_nil.
auto.
Qed.


(** VER qual é a melhor precedência para |-> (tá com a mesma do =??)**)

Lemma consSubst_app_3:
forall x a y F e G,
  length x = length F -> length y = length G -> ~ In a x ->
    (x++(a::y) |-> F ++ e::G) a = Some e.
Proof.
intros.
rewrite consSubst_app_2.
+simpl.
 destruct (string_dec a a).
 -auto.
 -intuition.
+auto.
+simpl; auto.
+auto.
Qed.

Lemma consSubst_None:
forall x F s,
  length x = length F -> ~ In s x ->
    (x|-> F) s = None.
Proof.
induction x.
+intros. auto.
+intros. destruct F.
 -auto.
 -simpl in H0.
  assert (a<>s /\ ~ In s x).
  split.
  {auto. }
  {auto. }
  destruct H1.
  simpl.
  destruct (string_dec s a).
  {symmetry in e. contradiction. }
  {rewrite IHx.
   +auto. +auto. +auto. }
Qed.



(*** Fazer com In s x <-> exists a x1,x2, x = x1 ++ a::x2 *)
Lemma consSubst_identity_1:
forall x s,
  In s x -> (x |-> map AVar x) s = Some (AVar s).
Proof.
induction x.
+contradiction.
+simpl.
 intros.
 destruct H.
 -rewrite H.
  destruct (string_dec s s).
  {auto. }
  {intuition. }
 -destruct (string_dec s a).
  {rewrite e. reflexivity. }
  {apply IHx. auto. }
Qed.


Lemma consSubst_identity_2:
forall x s,
  ~ In s x -> (x |-> map AVar x) s = None.
Proof.
induction x.
+intros. simpl. auto.
+intros.
 simpl in H.
 assert (a<>s /\ ~ In s x).
 {tauto. }
 destruct H0.
 simpl.
 destruct (string_dec s a).
 -rewrite e in H0. intuition.
 -apply IHx. auto.
Qed.

Lemma subst_identity :
forall (x y:list string) (F:list exp) (e:exp),
 length x = length F ->
    subst ((x,y) |-> (F,map AVar y)) e = subst (x|->F) e.
Proof.
intros.
induction e; simpl;auto.
+simpl. rewrite IHe1. rewrite IHe2. auto.
+simpl. rewrite IHe1. rewrite IHe2. auto. 
+simpl. rewrite IHe1. rewrite IHe2. auto. 
+ destruct (in_dec string_dec s x);auto.
 - rewrite consSubst_app_1;auto.
    { symmetry. apply map_length. }
 - assert ((x |-> F) s = None).
  {apply consSubst_None; auto. }
  rewrite H0.
  rewrite consSubst_app_2;auto.
  {destruct (in_dec string_dec s y).
   + rewrite consSubst_identity_1; auto.
   + rewrite consSubst_identity_2;auto. }
  {symmetry. apply map_length. }
+ simpl. rewrite IHe1. rewrite IHe2. auto. 
+ simpl. rewrite IHe1. rewrite IHe2. auto. 
+ simpl. rewrite IHe. auto. 
+ simpl. rewrite IHe1. rewrite IHe2. auto. 
+ simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. auto. 
Qed.

Lemma not_in_app:
forall A (a:A) (x y:list A),
  ~In a (x ++ y) <-> ~In a x /\ ~In a y.
Proof.
induction x.
+tauto.
+intros.
 simpl.
 assert (~ In a (x, y) <-> ~ In a x /\ ~ In a y).
 {apply IHx. }
 tauto.
Qed.


Lemma NoDup_app:
forall A (l l':list A) (a:A), NoDup (l++l') -> In a l -> ~ In a l'.
Proof.
intros.
induction l.
+auto.
+change ((a0::l) ++ l') with (a0 :: (l ++ l')) in H.
 rewrite NoDup_cons_iff in H.
 rewrite not_in_app in H.
 simpl in H0.
 destruct H0.
 - rewrite H0 in H. tauto.
 -tauto.
Qed.

Lemma NoDup_app_comm:
forall A (x y:list A), NoDup (x++y) <-> NoDup (y++x).
Proof.
intros.
induction x.
+simpl. rewrite app_nil_r. reflexivity.
+simpl.
 rewrite NoDup_cons_iff.
 rewrite not_in_app.
 rewrite IHx.
 assert (Add a (y++x) (y ++ a::x)).
 {apply Add_app. }
 symmetry.
 rewrite (NoDup_Add H).
 rewrite not_in_app.
tauto.
Qed.


Lemma consSubst_comm:
forall x y F G,
  length x = length F -> length y = length G -> NoDup (x++y) ->
  x++y |-> F++G = (y++x |-> G++F).
Proof.
intros.
assert (forall s, (x++y |-> F++G) s = (y++x |-> G++F) s).
+intros.
 destruct (in_dec string_dec s (x++y)).
 -destruct (in_dec string_dec s x).
  {assert (~ In s y).
   {apply (NoDup_app string x). auto. auto. }
   rewrite consSubst_app_1.
   rewrite consSubst_app_2.
   auto. auto. auto. auto. auto. auto. auto. }
  {assert (In s y). 
   {apply in_app_or in i. destruct i. contradiction. auto. }
   rewrite consSubst_app_2.
   rewrite consSubst_app_1.
   auto. auto. auto. auto. auto. auto. auto. }
 -apply not_in_app in n. destruct n.
  rewrite consSubst_app_2.
  rewrite consSubst_app_2.
  rewrite consSubst_None.
  rewrite consSubst_None.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
+apply functional_extensionality in H2. auto.
Qed.

Theorem substL_1:
forall (x y: list string) (F G  : list exp),
length x == length F ->
NoDup (x++y) ->
substL ((x,y) |-> (F,map AVar y)) G == substL (x |-> F) G.
induction G ; intuition.
simpl.
rewrite subst_identity; auto.
rewrite H2; auto. Qed.

Theorem substL_2:
forall (x y z: list string)  (F G H J  : list exp),
length x = length F ->
length y = length G -> 
NoDup (x,y)->
substL ((x, y) |-> (F, G)) (H, J) ==
(substL ((x, y) |-> (F, G)) H, substL ((x, y) |-> (F, G)) J).
intros.
induction H; intuition.
simpl. rewrite IHlist; intuition. Save.

Theorem substL_3:
forall (x y z: list string)  (F G  : list exp),
length x = length F ->
length y = length G -> 
NoDup (x,y)->
substL ((x,y)|->(F,G)) (map AVar x) == F.
Admitted.

Theorem substL_4:
forall (x y z: list string)  (F G H J  : list exp),
length x = length F ->
length y = length G -> 
NoDup (x,y)->
substL ((x, y) |-> (F, G)) ((map AVar x, H), J) ==
(F, substL ((x, y) |-> (F, G)) (H, J)).
intros.
repeat(rewrite substL_2); intuition.
rewrite substL_3;intuition. Save.

Theorem NoDup_1 :
forall (A : Type) (x y z : list A),
NoDup (x,y,z) -> NoDup (x,y).
Admitted.

Theorem assigment_reduce :
forall (x y z : list string) (F G H J: list exp),
length x = length F -> 
length y = length G -> 
length y = length H ->
length z = length J ->
NoDup (x,y,z) ->
(((x,y) ::= (F,G));((y,z) ::= (H,J))) ==
((x,y,z) ::= (F, (substL ((x,y) |-> (F,G)) H), (substL ((x,y) |-> (F,G)) J))).
Proof.
intros.
assert (((x,y) ::= (F,G)) == ((x,y,z) ::= (F,G,map AVar z))) as H5.
  {rewrite assigment_3; auto. repeat(rewrite app_length). intuition. }
rewrite H5.
assert (((y, z) ::= (H, J)) == ((y,z,x) ::= (H, J, map AVar x))) as H6.
  {rewrite assigment_3;auto. repeat(rewrite app_length). intuition. }
rewrite H6.
assert (((y,z,x) ::= (H, J, map AVar x)) == ((x,y,z) ::= ( map AVar x, H, J))) as H7.
  { apply assigment_4_0;intuition. rewrite map_length; auto. }
rewrite H7.
rewrite assigment_1.
assert (substL (((x, y), z) |-> ((F, G), map AVar z)) ((map AVar x, H), J) ==
      substL (((x, y)) |-> ((F, G))) ((map AVar x, H), J) ) as H8.
  {rewrite substL_1;auto. repeat(rewrite app_length). intuition. }
rewrite H8.
apply NoDup_1 in H4.
repeat(rewrite substL_2); intuition.
rewrite substL_3; intuition. Save.

Theorem assignment_reduce_2:
forall (x y : list string) (E F : list exp),
length x = length E ->
length y = length F ->
NoDup (x,y) ->
x::=E; y::=F == x,y ::= E,substL (x|->E) F.
intros.
assert ((y::=F) == ((y,x)) ::= (F, (map AVar x))).
  - symmetry. rewrite assigment_3; intuition.
  - assert ((x::=E) == ((x,y) ::= (E, (map AVar y)))).
    + symmetry. rewrite assigment_3; intuition.
    + rewrite H2. 
      rewrite H3. 
      assert (y, x ::= F, map AVar x ==  x,y ::= map AVar x,F).
      { rewrite assigment_4_1;intuition. rewrite map_length;auto. } 
      rewrite H4.      
      rewrite assigment_1.
      rewrite substL_2;intuition.
      rewrite substL_3;intuition.
      rewrite substL_1; intuition.
      rewrite map_length; intuition.
      rewrite map_length; intuition. 
Save.

(*************** Normal Form ****************************)


Theorem NormalForm_SKIP :
forall (x:list string),
SKIP =(conditional BTrue (x::= (map AVar x)) ABORT ).
intros.
rewrite assigment_2.
rewrite conditional_true_1.
reflexivity.
Save.

Theorem NormalForm_ABORT :
forall (x:list string),
ABORT = (conditional BFalse (x::= (map AVar x)) ABORT ).
intros.
rewrite conditional_false_2.
reflexivity.
Save.

Theorem NormalForm_nondeterminism :
forall (P Q : command) (b c : exp),
nondeterminism (conditional b P ABORT) (conditional c Q ABORT) =
conditional (BCond b c BFalse) (nondeterminism P Q) ABORT.
intros.
(** Passo 1**)
rewrite conditional_nondeterminism_10.
(** Passo 2 **)
rewrite nondeterminism_symmetry.
rewrite conditional_nondeterminism_10.
rewrite nondeterminism_symmetry.
assert ((nondeterminism ABORT (conditional c Q ABORT)) = (nondeterminism (conditional c Q ABORT) ABORT) ).
  {rewrite nondeterminism_symmetry; reflexivity. }
rewrite H.
rewrite conditional_nondeterminism_10.
assert( nondeterminism ABORT P = nondeterminism P ABORT).
  { rewrite nondeterminism_symmetry; reflexivity. }
rewrite H0.
repeat(rewrite nondeterminism_zeroAbort).
rewrite conditional_idempotence_3.
(** Passo 3 **)
assert (conditional BFalse ABORT ABORT = ABORT).
  {rewrite conditional_false_2; reflexivity. }
rewrite <- H1.
rewrite conditional_cond_6. 
symmetry. 
repeat(rewrite conditional_false_2);reflexivity. 
Save.

(**
Provas a fazer
vars e = free ([isdef e])

l ::= substL (t|->e) l0 = substC l:=l0 t e



****Conditional*****


**)

Axiom vars_isdefExp :
forall (e:exp),
vars e = vars (isdef e).

Theorem vars_Free :
forall (e: exp),
vars e = free ([isdef e]).
intuition.
simpl.
rewrite app_nil_r.
apply vars_isdefExp.
Save.
(**
Notation " d '[' x '\' e ']' " := (substL (x |-> e) d) (at level 80, no associativity) .

Theorem subst_equivalence :
forall (x:list string) (y:string) (g : list exp) (e:exp),
x ::= (g[y::nil\e::nil]) = substC (x::=g) y e.
intros.
intuition.
Save.
**)
Theorem subst_equivalence :
forall (x:list string) (y:string) (g : list exp) (e:exp),
x ::= substL (y::nil|-> e::nil) g = substC (x::=g) y e.
intros.
intuition.
Save.

Theorem var_03_derivation:
forall (x:string) (p:list string) (e:list exp) (d : exp) (c:command),
varDeclaration x ((p,(x::nil))::=(e,(d::nil))) == varDeclaration x ([isdef d]; p::=e).
intros.
assert ((p, (x :: nil) ::= e, (d :: nil)) == (SKIP;(p, (x :: nil) ::= e, (d :: nil)))).
rewrite seqcomp_unitSKIP3_2;intuition.
rewrite H.
rewrite var_03.
rewrite seqcomp_unitSKIP3_2;intuition.
Save.

Theorem assignment_assertion:
forall (t : string) (e: exp),
~ In t (vars e) ->
varDeclaration t (t :: nil ::= e :: nil) == ([isdef e]).
intros.
Variable y : list string.
assert (t :: nil ::= e :: nil = ((t :: nil), y) ::= ((e :: nil), (map AVar y)) ).
+ symmetry. rewrite assigment_3; intuition.
+ rewrite H0. rewrite assigment_4_1; intuition.
  - assert (varDeclaration t (y, (t :: nil) ::= map AVar y, (e :: nil)) = varDeclaration t (SKIP ; (y, (t :: nil) ::= map AVar y, (e :: nil)))).
    { rewrite seqcomp_unitSKIP3_2; auto. }
rewrite H1.
rewrite var_03.
rewrite seqcomp_unitSKIP3_2.
rewrite assigment_2.
rewrite seqcomp_unitSKIP2_2.
rewrite var_08; auto.
rewrite <- vars_Free; intuition.
- rewrite map_length; auto.
Save.

Theorem InlineTemp :
forall (t : string) (e: exp) (c:command),
readonly t c ->
~ In t (vars e) -> 
(forall x, In x (vars e) -> readonly x c) ->
varDeclaration t ((t::nil ::= e::nil) ; c ) == [(isdef e)]; substC c t e.
induction c.
  + intros.
    simpl.
    repeat (rewrite seqcomp_unitSKIP2_2).
    rewrite assignment_assertion; try (auto).
  + intros.
    simpl. 
    repeat (rewrite seqcomp_zeroABORT2_3). 
    rewrite var_08; intuition.
  + intros.
    rewrite assignment_reduce_2;intuition.
    rewrite assigment_4_1;intuition.
    rewrite var_03_derivation; intuition.
    { rewrite subst_equivalence.
      rewrite var_08. reflexivity.
      simpl.
      




