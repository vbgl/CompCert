Require Import ssreflect.
Require Gigot.
Import AST Globalenvs Smallstep Linking Csharpminor Gigot.

Definition match_prog (p q: program) : Prop :=
  match_program
    (fun p f1 f2 =>
       f2 = transl_fundef (check_eligibility p) f1)
    eq
    p q.

Theorem transl_program_match (p: program) :
  match_prog p (transl_program p).
Proof. now apply match_transform_program_contextual. Qed.

Lemma id_transf (p: program) :
  p = AST.transform_program (fun f0 => AST.transf_fundef (fun f1 => f1) f0) p.
Proof.
unfold AST.transform_program.
destruct p as [ defs pubs main ]; f_equal; simpl.
induction defs as [ | (n, d) defs ih ]; auto.
simpl; f_equal; auto.
destruct d as [ [] | ] ; auto.
Qed.

Transparent Linker_prog Linker_def Linker_fundef.

Lemma linkorder_defIl (f1 f2: globdef fundef unit) :
  linkorder f1 f2 ->
  match f1 with
  | Gfun fd1 => exists fd2, f2 = Gfun fd2 /\ linkorder fd1 fd2
  | Gvar v1 => exists v2, f2 = Gvar v2 /\ linkorder v1 v2
  end.
Proof. move => h; case: h; eauto. Qed.

Lemma check_eligibility_mono (p q: program) :
  linkorder q p ->
  check_eligibility p = false ->
  check_eligibility q = false.
Proof.
intros [hmain [hpub hgd]]; unfold check_eligibility.
rewrite hmain; clear hmain.
generalize (hgd (prog_main p)).
setoid_rewrite Genv.find_def_symbol.
destruct (Genv.find_symbol (Genv.globalenv q)); auto.
move => /(_ _ (ex_intro _ _ (conj eq_refl _))).
unfold Genv.find_funct_ptr.
destruct (Genv.find_def (Genv.globalenv q)) as [ [f|] | ]; auto.
case/(_ _ eq_refl) => gd [] [b'] [ -> -> ] [/linkorder_defIl [f'] [-> h] _].
inversion h; auto.
Qed.

Lemma match_prog_eq (p q: program) :
  check_eligibility p = false ->
  match_prog p q ->
  p = q.
Proof.
intros hpq; destruct p as [pd pp pm], q as [qd qp qm].
intros [hid [hmain hpub]]; simpl in *; f_equal; auto.
subst.
revert hid.
generalize pd at 2 3 => q.
elim: q qd hpq.
- by intros ? _; inversion 1.
- case => n gd defs ih qd q h; inversion h; clear h; subst.
  destruct H1. destruct b1. simpl in *. subst.
  f_equal. f_equal.
  inversion H0; subst. f_equal.
  rewrite (check_eligibility_mono _ _ H); auto. by case: (f1).
  inversion H; subst; auto.
  eapply ih; auto.
Qed.

Theorem transl_program_correct (p q: program) :
  match_prog p q ->
  forward_simulation (semantics p) (semantics q).
Proof.
intros hpq.
refine (forward_simulation_step (semantics p) (semantics q)
                                _ (fun x y => check_eligibility p = false /\ x = y) _ _ _).
- apply (Globalenvs.Genv.senv_match hpq).
- intros s [].
  assert (check_eligibility p = false) as Hp.
  + unfold check_eligibility, ge in *.
    rewrite H0 H1 H2 {H1 H2}.
    by case: f.
  + exists (Callstate f nil Kstop m0); split; auto.
    econstructor; eauto.
    now apply (Genv.init_mem_match hpq).
    rewrite (Genv.find_symbol_match hpq) (match_program_main hpq); eassumption.
    destruct (Genv.find_funct_ptr_match hpq _ H1) as [u [f' [Hf' [? Hu]]]]; subst f'.
    rewrite Hf'; clear Hf'.
    replace (check_eligibility u) with false.
    * now destruct f.
    * erewrite check_eligibility_mono; eauto.
- now intros ? ? ? [_ ->].
- simpl.
  intros s1 t s1' hStep s2 [hp <-]; exists s1'; split; auto.
  by rewrite <- (match_prog_eq _ _ hp hpq).
Qed.
