Require Csharpminor.
Import AST Globalenvs Csharpminor.

(*
Definition check_eligibility (p: program) : bool :=
  match Genv.init_mem p with
  | None => true
  | Some _ =>
  let ge := Genv.globalenv p in
  match Genv.find_symbol ge p.(prog_main) with
  | None => true
  | Some b =>
  match Genv.find_funct_ptr ge b with
  | None => true
  | Some f =>
    if signature_eq (funsig f) signature_main
    then false else true
  end end end.
*)

Definition check_eligibility (p: program) : bool :=
  let ge := Genv.globalenv p in
  match Genv.find_symbol ge p.(prog_main) with
  | None => false
  | Some b =>
  match Genv.find_funct_ptr ge b with
  | None | Some (External _) => false
  | Some f =>
    if signature_eq (funsig f) signature_main
    then false else true
  end end.

Definition transl_function (b: bool) (f: function) : function :=
  if b then {|
    fn_sig := signature_main;
    fn_params := nil;
    fn_vars := nil;
    fn_temps := nil;
    fn_body := Sreturn (Some (Econst (Ointconst Integers.Int.zero)));
  |}
  else f.

Definition transl_fundef (b: bool) (f: fundef) : fundef :=
  transf_fundef (transl_function b) f.

Definition transl_program (p: program) : program :=
  transform_program (transl_fundef (check_eligibility p)) p.
