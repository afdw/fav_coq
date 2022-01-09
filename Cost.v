From Ltac2 Require Import Ltac2.
From Ltac2 Require Message.
From Ltac2 Require Constr.

Set Default Proof Mode "Classic".

Ltac2 mutable registered_cost_functions : unit -> (constr * constr) list := fun () => [].

Ltac2 cost_sum a_cost b_cost :=
  Constr.Unsafe.make (Constr.Unsafe.App 'plus (Array.of_list [a_cost; b_cost])).

Ltac2 rec count_lambda_depth constr :=
  match Constr.Unsafe.kind constr with
  | Constr.Unsafe.Lambda args body => Int.add (count_lambda_depth body) 1
  | _ => 0
  end.

Ltac2 rec to_prod_nat type_constr i n :=
  if Int.equal i n
  then 'nat
  else
    match Constr.Unsafe.kind type_constr with
    | Constr.Unsafe.Prod param body =>
      Constr.Unsafe.make (Constr.Unsafe.Prod param (to_prod_nat body (Int.add i 1) n))
    | _ =>
      Message.print (Message.of_string
        "Warning: compute_time can not handle fixpoint with non-prod type");
      type_constr
    end.

Ltac2 rec compute_cost input_constr :=
  let try_builtin input_constr fallback :=
    match List.assoc_opt Constr.equal input_constr (registered_cost_functions ()) with
    | Some result_constr =>
      Message.print (Message.of_int (List.length (registered_cost_functions ())));
      result_constr
    | None => fallback ()
    end in
  Message.print (Message.concat (Message.of_string "Trace: compute_time ") (Message.of_constr input_constr));
  let result_constr :=
    try_builtin input_constr (fun () =>
      match Constr.Unsafe.kind input_constr with
      | Constr.Unsafe.Rel rel => '1
      | Constr.Unsafe.Var var => '1
      | Constr.Unsafe.Lambda arg body =>
        let body_cost := compute_cost body in
        Constr.Unsafe.make (Constr.Unsafe.Lambda arg body_cost)
      | Constr.Unsafe.Constructor cstr instance => '1
      | Constr.Unsafe.Case ci c iv t bl =>
        let c_replacement := match Constr.Unsafe.kind c with
        | Constr.Unsafe.Lambda arg body => Constr.Unsafe.make (Constr.Unsafe.Lambda arg 'nat)
        | _ =>
          Message.print (Message.of_string
            "Warning: compute_time can not handle match with non-lambda 'c'");
          c
        end in
        match iv with
        | Constr.Unsafe.NoInvert => ()
        | Constr.Unsafe.CaseInvert _ =>
          Message.print (Message.of_string
            "Warning: compute_time can not handle match with CaseInvert; what it even means?")
        end;
        let bl_costs := Array.map compute_cost bl in
        Constr.Unsafe.make (Constr.Unsafe.Case ci c_replacement iv t bl_costs)
      | Constr.Unsafe.Fix recs i nas cs =>
        let nas_replacements := Array.mapi (fun i binder =>
          Constr.Binder.make
            (Constr.Binder.name binder)
            (to_prod_nat (Constr.Binder.type binder) 0 (count_lambda_depth (Array.get cs i)))
        ) nas in
        let cs_costs := Array.map compute_cost cs in
        Constr.Unsafe.make (Constr.Unsafe.Fix recs i nas_replacements cs_costs)
      | Constr.Unsafe.App fun_ args =>
        let fun_cost :=
          match Constr.Unsafe.kind fun_ with
          | Constr.Unsafe.Constructor _ _ => '1
          | Constr.Unsafe.Rel rel =>
            Constr.Unsafe.make (Constr.Unsafe.App (Constr.Unsafe.make (Constr.Unsafe.Rel rel)) args)
          | _ =>
            let cost_fun := try_builtin fun_ (fun () =>
              let fun_red := eval red in $fun_ in
              compute_cost fun_red
            ) in
            Constr.Unsafe.make (Constr.Unsafe.App cost_fun args)
          end in
        let args_costs := Array.map compute_cost args in
        let args_cost := Array.fold_left cost_sum '0 args_costs in
        cost_sum fun_cost args_cost
      | _ => Control.throw Match_failure
      end
    ) in
  Message.print (Message.concat (Message.of_string "Trace:           ^- ") (Message.of_constr result_constr));
  result_constr.

Ltac2 refine_compute_cost input_constr :=
  Control.refine (fun () =>
    let result_constr := compute_cost input_constr in
    eval simpl in $result_constr
  ).

Definition mul_cost n m := ltac2:(refine_compute_cost '(n * m)).

Ltac2 default_registered_cost_functions () :=
  [
    ('plus, '(fun (_ _ : nat) => 1));
    ('Nat.mul, '(fun (_ _ : nat) => 1))
  ].
Ltac2 Set registered_cost_functions := fun () => default_registered_cost_functions ().

Fixpoint nat_id n :=
  match n with
  | 0 => 0
  | S n' => S (nat_id n')
  end.

Definition nat_id_cost n := ltac2:(refine_compute_cost '(nat_id n)).

Fixpoint is_even n :=
  match n with
  | 0 => true
  | S n' => is_odd n'
  end
with is_odd n :=
  match n with
  | 0 => false
  | S n' => is_even n'
  end.

Definition is_even_cost n := ltac2:(refine_compute_cost '(is_even n)).

Fixpoint factorial n :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.

Definition factorial_cost n := ltac2:(refine_compute_cost '(factorial n)).
