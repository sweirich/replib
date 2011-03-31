Add LoadPath "metatheory".
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metatheory.
Require Export LibLNgen.

Require Export Unbound.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)

(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac destruct_sum :=
  let rec main x :=
    match type of x with
      | or _ _ => destruct x
      | sumbool _ _ => destruct x
      | sumor _ _ => destruct x
      | FindResult => destruct x
      | NthResult => destruct x
    end
  in
  match goal with
    | |- context [?x] => main x
    | H : _ |- _ => main H
    | _ : context [?x] |- _ => main x
  end.


Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_term_min_mutual :
(forall t1, 1 <= size_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_term_min :
forall t1, 1 <= size_term t1.
Proof.
pose proof size_term_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_min : lngen.

(* begin hide *)

Lemma size_term_close_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  size_term (close_term_wrt_term_rec n1 x1 t1) = size_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_close_term_wrt_term_rec :
forall t1 x1 n1,
  size_term (close_term_wrt_term_rec n1 x1 t1) = size_term t1.
Proof.
pose proof size_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_close_term_wrt_term_rec : lngen.
Hint Rewrite size_term_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_term_close_term_wrt_term :
forall t1 x1,
  size_term (close_term_wrt_term x1 t1) = size_term t1.
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_close_term_wrt_term : lngen.
Hint Rewrite size_term_close_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_mutual :
(forall t1 t2 n1,
  size_term t1 <= size_term (open_term_wrt_term_rec n1 t2 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec :
forall t1 t2 n1,
  size_term t1 <= size_term (open_term_wrt_term_rec n1 t2 t1).
Proof.
pose proof size_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma size_term_open_term_wrt_term :
forall t1 t2,
  size_term t1 <= size_term (open_term_wrt_term t1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_term : lngen.

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_var_mutual :
(forall t1 p1 n1,
  size_term (open_term_wrt_term_rec n1 p1 t1) = size_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_var :
forall t1 p1 n1,
  size_term (open_term_wrt_term_rec n1 p1 t1) = size_term t1.
Proof.
pose proof size_term_open_term_wrt_term_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_term_rec_var : lngen.
Hint Rewrite size_term_open_term_wrt_term_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_term_open_term_wrt_term_var :
forall t1 p1,
  size_term (open_term_wrt_term t1 p1) = size_term t1.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_term_var : lngen.
Hint Rewrite size_term_open_term_wrt_term_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma app_nth1 : forall A, forall x : A, forall n l l', 
  nth_error l n = Some x -> nth_error (l ++ l') n = Some x.
induction n.
default_simp. destruct l; default_simp.
default_simp. destruct l; default_simp.
Qed.

Hint Resolve app_nth1 : lngen.

Lemma degree_term_wrt_term_S_mutual :
(forall n1 n2 t1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term  (n1 ++ n2) t1).
Proof.
apply_mutual_ind degree_term_wrt_term_mutind;
default_simp; intuition eauto using app_nth1.
Qed.

(* end hide *)

Lemma degree_term_wrt_term_S :
forall n1 n2 t1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term (n1 ++ n2) t1.
Proof.
pose proof degree_term_wrt_term_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_S : lngen.

Lemma degree_term_wrt_term_O :
forall n1 t1,
  degree_term_wrt_term nil t1 ->
  degree_term_wrt_term n1 t1.
Proof. 
intros n1 t1.
replace n1 with (nil ++ n1). auto with lngen. auto.
Qed.

Hint Resolve degree_term_wrt_term_O : lngen.

(* begin hide *)

Lemma lookup_inrange : forall x p n1 n2, 
  length (binders p) = n1 ->
  index n2 = find x p     ->
  n2 < n1.
induction p; intros; simpl in *; try inversion H0.
destruct (x == n); subst; try inversion H0; auto.
pose (K1 := IHp1 n1 n2).
destruct (find x p1). simpl in *. inversion H0. subst.
Admitted.
(*
assert (P : length (binders p1) <= length (binders p1 ++ binders p2)).
apply lt_le_trans with (m := length(binders p1)).
apply IHp1 with (n1 := length (binders p1)). auto.  auto.
*)

Lemma app_nth_length : forall A l1 (x:A) l3,
  nth_error (l1 ++ (x :: l3)) (length l1) = Some x.
Admitted.

Lemma degree_term_wrt_term_close_term_wrt_term_rec_mutual :
(forall t1 x1 n n1,
  degree_term_wrt_term n1 t1 ->
  length (binders x1) = n ->
  degree_term_wrt_term (n1 ++ (n :: nil)) (close_term_wrt_term_rec (length n1) x1 t1)).
Proof.
apply_mutual_ind term_mutind. default_simp.
intros.
simpl.
remember (find n x1) as p.
destruct p. 
eapply degree_wrt_term_var_b with (n4 := n0). 
Focus 3.
default_simp.
Focus 5.
Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec :
forall n t1 x1 n1,
  degree_term_wrt_term n1 t1 ->
  length (binders x1) = n -> 
  degree_term_wrt_term (n1 ++ (n :: nil)) (close_term_wrt_term_rec (length n1) x1 t1).
Proof.
pose proof degree_term_wrt_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_close_term_wrt_term_rec : lngen.

(* end hide *)

Lemma degree_term_wrt_term_close_term_wrt_term :
forall t1 x1 n,
  degree_term_wrt_term nil t1 ->
  length (binders x1) = n -> 
  degree_term_wrt_term (n :: nil) (close_term_wrt_term x1 t1).
Proof.
unfold close_term_wrt_term; default_simp.
Admitted.

Hint Resolve degree_term_wrt_term_close_term_wrt_term : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_inv_mutual :
(forall n t1 x1 n1,
  length (binders x1) = n ->
  degree_term_wrt_term (n1 ++ (n :: nil)) (close_term_wrt_term_rec (length n1) x1 t1) ->
  degree_term_wrt_term n1 t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
inversion H0. subst.
eapply degree_wrt_term_var_b.
Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_inv :
forall t1 x1 n1,
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 t1) ->
  degree_term_wrt_term n1 t1.
Proof.
pose proof degree_term_wrt_term_close_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_term_rec_inv : lngen.

(* end hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_inv :
forall t1 x1,
  degree_term_wrt_term 1 (close_term_wrt_term x1 t1) ->
  degree_term_wrt_term 0 t1.
Proof.
unfold close_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_term_inv : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_mutual :
(forall t1 t2 n1,
  degree_term_wrt_term (S n1) t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec :
forall t1 t2 n1,
  degree_term_wrt_term (S n1) t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1).
Proof.
pose proof degree_term_wrt_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma degree_term_wrt_term_open_term_wrt_term :
forall t1 t2,
  degree_term_wrt_term 1 t1 ->
  degree_term_wrt_term 0 t2 ->
  degree_term_wrt_term 0 (open_term_wrt_term t1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_term : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_inv_mutual :
(forall t1 t2 n1,
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1) ->
  degree_term_wrt_term (S n1) t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_inv :
forall t1 t2 n1,
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1) ->
  degree_term_wrt_term (S n1) t1.
Proof.
pose proof degree_term_wrt_term_open_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_term_rec_inv : lngen.

(* end hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_inv :
forall t1 t2,
  degree_term_wrt_term 0 (open_term_wrt_term t1 t2) ->
  degree_term_wrt_term 1 t1.
Proof.
unfold open_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_term_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_term_wrt_term_rec_inj_mutual :
(forall t1 t2 x1 n1,
  close_term_wrt_term_rec n1 x1 t1 = close_term_wrt_term_rec n1 x1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_inj :
forall t1 t2 x1 n1,
  close_term_wrt_term_rec n1 x1 t1 = close_term_wrt_term_rec n1 x1 t2 ->
  t1 = t2.
Proof.
pose proof close_term_wrt_term_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_term_wrt_term_rec_inj : lngen.

(* end hide *)

Lemma close_term_wrt_term_inj :
forall t1 t2 x1,
  close_term_wrt_term x1 t1 = close_term_wrt_term x1 t2 ->
  t1 = t2.
Proof.
unfold close_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate close_term_wrt_term_inj : lngen.

(* begin hide *)

Lemma close_term_wrt_term_rec_open_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 (open_term_wrt_term_rec n1 (var_f x1) t1) = t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_open_term_wrt_term_rec :
forall t1 x1 n1,
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 (open_term_wrt_term_rec n1 (var_f x1) t1) = t1.
Proof.
pose proof close_term_wrt_term_rec_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_term_rec_open_term_wrt_term_rec : lngen.
Hint Rewrite close_term_wrt_term_rec_open_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_term_wrt_term_open_term_wrt_term :
forall t1 x1,
  x1 `notin` fv_term t1 ->
  close_term_wrt_term x1 (open_term_wrt_term t1 (var_f x1)) = t1.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve close_term_wrt_term_open_term_wrt_term : lngen.
Hint Rewrite close_term_wrt_term_open_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma open_term_wrt_term_rec_close_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  open_term_wrt_term_rec n1 (var_f x1) (close_term_wrt_term_rec n1 x1 t1) = t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_close_term_wrt_term_rec :
forall t1 x1 n1,
  open_term_wrt_term_rec n1 (var_f x1) (close_term_wrt_term_rec n1 x1 t1) = t1.
Proof.
pose proof open_term_wrt_term_rec_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_term_rec_close_term_wrt_term_rec : lngen.
Hint Rewrite open_term_wrt_term_rec_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_term_wrt_term_close_term_wrt_term :
forall t1 x1,
  open_term_wrt_term (close_term_wrt_term x1 t1) (var_f x1) = t1.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve open_term_wrt_term_close_term_wrt_term : lngen.
Hint Rewrite open_term_wrt_term_close_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma open_term_wrt_term_rec_inj_mutual :
(forall t2 t1 x1 n1,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 (var_f x1) t2 = open_term_wrt_term_rec n1 (var_f x1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_inj :
forall t2 t1 x1 n1,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 (var_f x1) t2 = open_term_wrt_term_rec n1 (var_f x1) t1 ->
  t2 = t1.
Proof.
pose proof open_term_wrt_term_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_term_wrt_term_rec_inj : lngen.

(* end hide *)

Lemma open_term_wrt_term_inj :
forall t2 t1 x1,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  open_term_wrt_term t2 (var_f x1) = open_term_wrt_term t1 (var_f x1) ->
  t2 = t1.
Proof.
unfold open_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate open_term_wrt_term_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_term_wrt_term_of_lc_term_mutual :
(forall t1,
  lc_term t1 ->
  degree_term_wrt_term 0 t1).
Proof.
apply_mutual_ind lc_term_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_term_wrt_term_of_lc_term :
forall t1,
  lc_term t1 ->
  degree_term_wrt_term 0 t1.
Proof.
pose proof degree_term_wrt_term_of_lc_term_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_of_lc_term : lngen.

(* begin hide *)

Lemma lc_term_of_degree_size_mutual :
forall i1,
(forall t1,
  size_term t1 = i1 ->
  degree_term_wrt_term 0 t1 ->
  lc_term t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind term_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_term_of_degree :
forall t1,
  degree_term_wrt_term 0 t1 ->
  lc_term t1.
Proof.
intros t1; intros;
pose proof (lc_term_of_degree_size_mutual (size_term t1));
intuition eauto.
Qed.

Hint Resolve lc_term_of_degree : lngen.

Ltac term_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_term_wrt_term_of_lc_term in J1; clear H
          end).

Lemma lc_bind_exists :
forall x1 p1 t1,
  lc_term p1 ->
  lc_term (open_term_wrt_term t1 (var_f x1)) ->
  lc_term (bind p1 t1).
Proof.
intros; term_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_rebind_exists :
forall x1 p1 t1,
  lc_term p1 ->
  lc_term (open_term_wrt_term t1 (var_f x1)) ->
  lc_term (rebind p1 t1).
Proof.
intros; term_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_rec_exists :
forall x1 p1,
  lc_term (open_term_wrt_term p1 (var_f x1)) ->
  lc_term (rec p1).
Proof.
intros; term_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_term (bind _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_bind_exists x1).

Hint Extern 1 (lc_term (rebind _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_rebind_exists x1).

Hint Extern 1 (lc_term (rec _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_rec_exists x1).

Lemma lc_body_term_wrt_term :
forall t1 t2,
  body_term_wrt_term t1 ->
  lc_term t2 ->
  lc_term (open_term_wrt_term t1 t2).
Proof.
unfold body_term_wrt_term;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
term_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_term_wrt_term : lngen.

Lemma lc_body_bind_2 :
forall p1 t1,
  lc_term (bind p1 t1) ->
  body_term_wrt_term t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_bind_2 : lngen.

Lemma lc_body_rebind_2 :
forall p1 t1,
  lc_term (rebind p1 t1) ->
  body_term_wrt_term t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_rebind_2 : lngen.

Lemma lc_body_rec_1 :
forall p1,
  lc_term (rec p1) ->
  body_term_wrt_term p1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_rec_1 : lngen.

(* begin hide *)

Lemma lc_term_unique_mutual :
(forall t1 (proof2 proof3 : lc_term t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_term_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_term_unique :
forall t1 (proof2 proof3 : lc_term t1), proof2 = proof3.
Proof.
pose proof lc_term_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_term_unique : lngen.

(* begin hide *)

Lemma lc_term_of_lc_set_term_mutual :
(forall t1, lc_set_term t1 -> lc_term t1).
Proof.
apply_mutual_ind lc_set_term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_term_of_lc_set_term :
forall t1, lc_set_term t1 -> lc_term t1.
Proof.
pose proof lc_term_of_lc_set_term_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_term_of_lc_set_term : lngen.

(* begin hide *)

Lemma lc_set_term_of_lc_term_size_mutual :
forall i1,
(forall t1,
  size_term t1 = i1 ->
  lc_term t1 ->
  lc_set_term t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind term_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_term_of_lc_term];
default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_term_of_lc_term :
forall t1,
  lc_term t1 ->
  lc_set_term t1.
Proof.
intros t1; intros;
pose proof (lc_set_term_of_lc_term_size_mutual (size_term t1));
intuition eauto.
Qed.

Hint Resolve lc_set_term_of_lc_term : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_term_wrt_term_rec_degree_term_wrt_term_mutual :
(forall t1 x1 n1,
  degree_term_wrt_term n1 t1 ->
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 t1 = t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_degree_term_wrt_term :
forall t1 x1 n1,
  degree_term_wrt_term n1 t1 ->
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 t1 = t1.
Proof.
pose proof close_term_wrt_term_rec_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_term_rec_degree_term_wrt_term : lngen.
Hint Rewrite close_term_wrt_term_rec_degree_term_wrt_term using solve [auto] : lngen.

(* end hide *)

Lemma close_term_wrt_term_lc_term :
forall t1 x1,
  lc_term t1 ->
  x1 `notin` fv_term t1 ->
  close_term_wrt_term x1 t1 = t1.
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve close_term_wrt_term_lc_term : lngen.
Hint Rewrite close_term_wrt_term_lc_term using solve [auto] : lngen.

(* begin hide *)

Lemma open_term_wrt_term_rec_degree_term_wrt_term_mutual :
(forall t2 t1 n1,
  degree_term_wrt_term n1 t2 ->
  open_term_wrt_term_rec n1 t1 t2 = t2).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_degree_term_wrt_term :
forall t2 t1 n1,
  degree_term_wrt_term n1 t2 ->
  open_term_wrt_term_rec n1 t1 t2 = t2.
Proof.
pose proof open_term_wrt_term_rec_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_term_rec_degree_term_wrt_term : lngen.
Hint Rewrite open_term_wrt_term_rec_degree_term_wrt_term using solve [auto] : lngen.

(* end hide *)

Lemma open_term_wrt_term_lc_term :
forall t2 t1,
  lc_term t2 ->
  open_term_wrt_term t2 t1 = t2.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve open_term_wrt_term_lc_term : lngen.
Hint Rewrite open_term_wrt_term_lc_term using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_term_close_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  fv_term (close_term_wrt_term_rec n1 x1 t1) [=] remove x1 (fv_term t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_close_term_wrt_term_rec :
forall t1 x1 n1,
  fv_term (close_term_wrt_term_rec n1 x1 t1) [=] remove x1 (fv_term t1).
Proof.
pose proof fv_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_close_term_wrt_term_rec : lngen.
Hint Rewrite fv_term_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_term_close_term_wrt_term :
forall t1 x1,
  fv_term (close_term_wrt_term x1 t1) [=] remove x1 (fv_term t1).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_close_term_wrt_term : lngen.
Hint Rewrite fv_term_close_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_lower_mutual :
(forall t1 t2 n1,
  fv_term t1 [<=] fv_term (open_term_wrt_term_rec n1 t2 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_lower :
forall t1 t2 n1,
  fv_term t1 [<=] fv_term (open_term_wrt_term_rec n1 t2 t1).
Proof.
pose proof fv_term_open_term_wrt_term_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_term_rec_lower : lngen.

(* end hide *)

Lemma fv_term_open_term_wrt_term_lower :
forall t1 t2,
  fv_term t1 [<=] fv_term (open_term_wrt_term t1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_term_lower : lngen.

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_upper_mutual :
(forall t1 t2 n1,
  fv_term (open_term_wrt_term_rec n1 t2 t1) [<=] fv_term t2 `union` fv_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_upper :
forall t1 t2 n1,
  fv_term (open_term_wrt_term_rec n1 t2 t1) [<=] fv_term t2 `union` fv_term t1.
Proof.
pose proof fv_term_open_term_wrt_term_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_term_rec_upper : lngen.

(* end hide *)

Lemma fv_term_open_term_wrt_term_upper :
forall t1 t2,
  fv_term (open_term_wrt_term t1 t2) [<=] fv_term t2 `union` fv_term t1.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_term_upper : lngen.

(* begin hide *)

Lemma fv_term_subst_term_fresh_mutual :
(forall t1 t2 x1,
  x1 `notin` fv_term t1 ->
  fv_term (subst_term t2 x1 t1) [=] fv_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_fresh :
forall t1 t2 x1,
  x1 `notin` fv_term t1 ->
  fv_term (subst_term t2 x1 t1) [=] fv_term t1.
Proof.
pose proof fv_term_subst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_fresh : lngen.
Hint Rewrite fv_term_subst_term_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_term_subst_term_lower_mutual :
(forall t1 t2 x1,
  remove x1 (fv_term t1) [<=] fv_term (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_lower :
forall t1 t2 x1,
  remove x1 (fv_term t1) [<=] fv_term (subst_term t2 x1 t1).
Proof.
pose proof fv_term_subst_term_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_lower : lngen.

(* begin hide *)

Lemma fv_term_subst_term_notin_mutual :
(forall t1 t2 x1 x2,
  x2 `notin` fv_term t1 ->
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_notin :
forall t1 t2 x1 x2,
  x2 `notin` fv_term t1 ->
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term (subst_term t2 x1 t1).
Proof.
pose proof fv_term_subst_term_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_notin : lngen.

(* begin hide *)

Lemma fv_term_subst_term_upper_mutual :
(forall t1 t2 x1,
  fv_term (subst_term t2 x1 t1) [<=] fv_term t2 `union` remove x1 (fv_term t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_upper :
forall t1 t2 x1,
  fv_term (subst_term t2 x1 t1) [<=] fv_term t2 `union` remove x1 (fv_term t1).
Proof.
pose proof fv_term_subst_term_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_mutual :
(forall t2 t1 x1 x2 n1,
  degree_term_wrt_term n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_term t1 ->
  subst_term t1 x1 (close_term_wrt_term_rec n1 x2 t2) = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 t2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_close_term_wrt_term_rec :
forall t2 t1 x1 x2 n1,
  degree_term_wrt_term n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_term t1 ->
  subst_term t1 x1 (close_term_wrt_term_rec n1 x2 t2) = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 t2).
Proof.
pose proof subst_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_term_rec : lngen.

Lemma subst_term_close_term_wrt_term :
forall t2 t1 x1 x2,
  lc_term t1 ->  x1 <> x2 ->
  x2 `notin` fv_term t1 ->
  subst_term t1 x1 (close_term_wrt_term x2 t2) = close_term_wrt_term x2 (subst_term t1 x1 t2).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_term : lngen.

(* begin hide *)

Lemma subst_term_degree_term_wrt_term_mutual :
(forall t1 t2 x1 n1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_degree_term_wrt_term :
forall t1 t2 x1 n1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (subst_term t2 x1 t1).
Proof.
pose proof subst_term_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_degree_term_wrt_term : lngen.

(* begin hide *)

Lemma subst_term_fresh_eq_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_term t2 ->
  subst_term t1 x1 t2 = t2).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh_eq :
forall t2 t1 x1,
  x1 `notin` fv_term t2 ->
  subst_term t1 x1 t2 = t2.
Proof.
pose proof subst_term_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh_eq : lngen.
Hint Rewrite subst_term_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_term_fresh_same_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x1 t2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh_same :
forall t2 t1 x1,
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x1 t2).
Proof.
pose proof subst_term_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh_same : lngen.
Hint Rewrite subst_term_fresh_same using solve [auto] : lngen.

(* begin hide *)

Lemma subst_term_fresh_mutual :
(forall t2 t1 x1 x2,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x2 t2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh :
forall t2 t1 x1 x2,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x2 t2).
Proof.
pose proof subst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh : lngen.
Hint Rewrite subst_term_fresh using solve [auto] : lngen.

Lemma subst_term_lc_term :
forall t1 t2 x1,
  lc_term t1 ->
  lc_term t2 ->
  lc_term (subst_term t2 x1 t1).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_lc_term : lngen.

(* begin hide *)

Lemma subst_term_open_term_wrt_term_rec_mutual :
(forall t3 t1 t2 x1 n1,
  lc_term t1 ->
  subst_term t1 x1 (open_term_wrt_term_rec n1 t2 t3) = open_term_wrt_term_rec n1 (subst_term t1 x1 t2) (subst_term t1 x1 t3)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_open_term_wrt_term_rec :
forall t3 t1 t2 x1 n1,
  lc_term t1 ->
  subst_term t1 x1 (open_term_wrt_term_rec n1 t2 t3) = open_term_wrt_term_rec n1 (subst_term t1 x1 t2) (subst_term t1 x1 t3).
Proof.
pose proof subst_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma subst_term_open_term_wrt_term :
forall t3 t1 t2 x1,
  lc_term t1 ->
  subst_term t1 x1 (open_term_wrt_term t3 t2) = open_term_wrt_term (subst_term t1 x1 t3) (subst_term t1 x1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_term : lngen.

Lemma subst_term_open_term_wrt_term_var :
forall t2 t1 x1 x2,
  x1 <> x2 ->
  lc_term t1 ->
  open_term_wrt_term (subst_term t1 x1 t2) (var_f x2) = subst_term t1 x1 (open_term_wrt_term t2 (var_f x2)).
Proof.
intros; rewrite subst_term_open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_term_var : lngen.

(* begin hide *)

Lemma subst_term_spec_rec_mutual :
(forall t1 t2 x1 n1,
  subst_term t2 x1 t1 = open_term_wrt_term_rec n1 t2 (close_term_wrt_term_rec n1 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_spec_rec :
forall t1 t2 x1 n1,
  subst_term t2 x1 t1 = open_term_wrt_term_rec n1 t2 (close_term_wrt_term_rec n1 x1 t1).
Proof.
pose proof subst_term_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_spec_rec : lngen.

(* end hide *)

Lemma subst_term_spec :
forall t1 t2 x1,
  subst_term t2 x1 t1 = open_term_wrt_term (close_term_wrt_term x1 t1) t2.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_spec : lngen.

(* begin hide *)

Lemma subst_term_subst_term_mutual :
(forall t1 t2 t3 x2 x1,
  x2 `notin` fv_term t2 ->
  x2 <> x1 ->
  subst_term t2 x1 (subst_term t3 x2 t1) = subst_term (subst_term t2 x1 t3) x2 (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_subst_term :
forall t1 t2 t3 x2 x1,
  x2 `notin` fv_term t2 ->
  x2 <> x1 ->
  subst_term t2 x1 (subst_term t3 x2 t1) = subst_term (subst_term t2 x1 t3) x2 (subst_term t2 x1 t1).
Proof.
pose proof subst_term_subst_term_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_subst_term : lngen.

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual :
(forall t2 t1 x1 x2 n1,
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term t1 ->
  x2 <> x1 ->
  degree_term_wrt_term n1 t1 ->
  subst_term t1 x1 t2 = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 (open_term_wrt_term_rec n1 (var_f x2) t2))).
Proof.
apply_mutual_ind term_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec :
forall t2 t1 x1 x2 n1,
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term t1 ->
  x2 <> x1 ->
  degree_term_wrt_term n1 t1 ->
  subst_term t1 x1 t2 = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 (open_term_wrt_term_rec n1 (var_f x2) t2)).
Proof.
pose proof subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma subst_term_close_term_wrt_term_open_term_wrt_term :
forall t2 t1 x1 x2,
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term t1 ->
  x2 <> x1 ->
  lc_term t1 ->
  subst_term t1 x1 t2 = close_term_wrt_term x2 (subst_term t1 x1 (open_term_wrt_term t2 (var_f x2))).
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_term_open_term_wrt_term : lngen.

Lemma subst_term_bind :
forall x2 p1 t2 t1 x1,
  lc_term t1 ->
  x2 `notin` fv_term t1 `union` fv_term t2 `union` singleton x1 ->
  subst_term t1 x1 (bind p1 t2) = bind (subst_term t1 x1 p1) (close_term_wrt_term x2 (subst_term t1 x1 (open_term_wrt_term t2 (var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_bind : lngen.

Lemma subst_term_rebind :
forall x2 p1 t2 t1 x1,
  lc_term t1 ->
  x2 `notin` fv_term t1 `union` fv_term t2 `union` singleton x1 ->
  subst_term t1 x1 (rebind p1 t2) = rebind (subst_term t1 x1 p1) (close_term_wrt_term x2 (subst_term t1 x1 (open_term_wrt_term t2 (var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_rebind : lngen.

Lemma subst_term_rec :
forall x2 p1 t1 x1,
  lc_term t1 ->
  x2 `notin` fv_term t1 `union` fv_term p1 `union` singleton x1 ->
  subst_term t1 x1 (rec p1) = rec (close_term_wrt_term x2 (subst_term t1 x1 (open_term_wrt_term p1 (var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_rec : lngen.

(* begin hide *)

Lemma subst_term_intro_rec_mutual :
(forall t1 x1 t2 n1,
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 t2 t1 = subst_term t2 x1 (open_term_wrt_term_rec n1 (var_f x1) t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_intro_rec :
forall t1 x1 t2 n1,
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 t2 t1 = subst_term t2 x1 (open_term_wrt_term_rec n1 (var_f x1) t1).
Proof.
pose proof subst_term_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_intro_rec : lngen.
Hint Rewrite subst_term_intro_rec using solve [auto] : lngen.

Lemma subst_term_intro :
forall x1 t1 t2,
  x1 `notin` fv_term t1 ->
  open_term_wrt_term t1 t2 = subst_term t2 x1 (open_term_wrt_term t1 (var_f x1)).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto := auto; tauto.
Ltac default_autorewrite := fail.
