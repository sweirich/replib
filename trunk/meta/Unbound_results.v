Add LoadPath "metatheory".
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metatheory.
Require Export LibLNgen.

Require Export Unbound.

Set Implicit Arguments.



Lemma beq_nat_sym : forall n1 n2 b, beq_nat n1 n2 = b -> beq_nat n2 n1 = b.
induction n1; destruct n2; simpl; auto.
Qed.

Lemma case_bool : forall b:bool, {b = true} + {b = false}.
intro b. destruct b. auto. auto.
Qed.

Lemma aeq_sym : forall t u m, aeq m t u = true -> aeq m u t = true.
induction t; intros u m; destruct m; destruct u; simpl in *; 
   try (intro H; 
        destruct (andb_prop _ _ H);
        rewrite (IHt1 _ _); auto;
        rewrite (IHt2 _ _); auto);
auto using beq_nat_sym.
destruct (case_bool (beq_nat n n1)).
rewrite e.
rewrite (beq_nat_sym n n1 e). 
auto using beq_nat_sym.
rewrite e. 
rewrite (beq_nat_sym n n1 e). auto.
destruct (case_bool (beq_nat n n1));
  rewrite e; rewrite (beq_nat_sym n n1 e); auto using beq_nat_sym.
destruct (n == n0); destruct (n0 == n); auto.
Qed.

Lemma beq_nat_trans : forall n1 n2 n3, beq_nat n1 n2 = true ->
  beq_nat n2 n3 = true -> beq_nat n1 n3 = true.
induction n1; destruct n2;
induction n3; simpl; auto. intros. inversion H.
apply IHn1.
Qed.

Lemma aeq_trans : forall s t u m, aeq m s t = true -> aeq m t u = true -> aeq m s u = true.
induction s; destruct t; destruct u; intro m; simpl; try (intro H; inversion H); auto.
Admitted.

Lemma aeq_fv : forall t1 t2 m, aeq m t1 t2 = true -> fv m t1 = fv m t2.
induction t1; destruct t2; intro m; simpl; try (intro H; inversion H); auto.
destruct m; simpl in *; 
  auto;
  try (destruct (andb_prop _ _ H);
      rewrite (IHt1_1 t2_1); auto;
      rewrite (IHt1_2 t2_2); auto);
  auto.
destruct (n == n0). subst. auto. inversion H.
destruct (andb_prop _ _ H).
rewrite (IHt1_1 t2_1); auto.
rewrite (IHt1_2 t2_2); auto.
destruct (andb_prop _ _ H).
rewrite (IHt1_1 t2_1); auto.
rewrite (IHt1_2 t2_2); auto. 
destruct (andb_prop _ _ H).
rewrite (IHt1_1 t2_1); auto.
rewrite (IHt1_2 t2_2); auto. 
Qed. 

Lemma aeq_subst : forall t1 t2 s1 s2 x m, 
  aeq m t1 t2 = true -> aeq Term s1 s2 = true -> 
  aeq m (subst m s1 x t1) (subst m s2 x t2) = true.
induction t1; destruct t2; intros s1 s2 x m; try (intro H; inversion H);
  try (destruct (andb_prop _ _ H1);
    rewrite H0; rewrite H2; simpl;
    intro J; rewrite IHt1_1; auto; rewrite IHt1_2; auto); auto.

destruct m.
  simpl. destruct (n == n0). subst. destruct (n0 == x). auto. auto.
    inversion H1.
  simpl. auto.
rewrite H1. intro J. simpl. rewrite IHt1; auto.
rewrite H1. intro J. simpl. rewrite IHt1; auto.
rewrite H1. intro J. simpl. rewrite IHt1; auto.
Qed.

Lemma aeq_freshen_pat : forall pat pat1 pat2 ns1 ns1' ns2 ns2' perm1 perm2,
  freshen pat1 ns1 nil = (pat, ns1', perm1) ->
  freshen pat2 ns2 nil = (pat, ns2', perm2) ->
  aeq Pat pat1 pat2 = true.
induction pat; destruct pat1; simpl; 
   intros pat2' ns1 ns1' ns2 ns2' perm1 perm2 J1 J2; try inversion J1; subst.
destruct pat2'; simpl in *; inversion J2. subst.
rewrite <- beq_nat_refl.
rewrite <- beq_nat_refl. auto.
destruct ns2;  inversion J2.

Lemma aeq_freshen : forall t1 t2 pat pat1 pat2 ns1 ns1' ns2 ns2' perm1 perm2,
  freshen Pat pat1 ns1 nil = (pat, ns1', perm1) ->
  freshen Pat pat2 ns2 nil = (pat, ns2', perm2) ->
  aeq Term (swaps perm1 t1) (swaps perm2 t2) = true ->
  aeq Term (bind pat1 t1) (bind pat2 t2) = true.
induction t1; destruct t2; simpl;
  intros pat pat1 pat2 ns1 ns1' ns2 ns2' perm1 perm2 H1 H2 H3;
  try inversion H3.
(* 1 *)
rewrite H3. 